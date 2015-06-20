#lang racket/base
;; Core implementation of network actors and Network Calculus (NC) communication API.

(require racket/set)
(require racket/match)
(require racket/list)
(require "route.rkt")
(require "gestalt.rkt")
(require "functional-queue.rkt")
(require "trace.rkt")
(require "tset.rkt")

(provide (struct-out routing-update)
	 (struct-out message)
	 (struct-out quit)
	 (except-out (struct-out spawn) spawn)
	 (rename-out [make-spawn spawn] [spawn <spawn>])
	 (struct-out process)
	 (struct-out transition)

	 (struct-out trigger-guard)

	 (except-out (struct-out world) world)

	 ;; imported from route.rkt:
	 ?
	 wildcard?
	 ?!
	 (struct-out capture)
	 pretty-print-matcher
	 matcher->pretty-string
	 matcher-empty?
	 (rename-out [projection->pattern matcher-projection->pattern]
		     [compile-projection compile-matcher-projection])

	 sub
	 pub
	 gestalt-accepts?
	 filter-event

	 send
	 feedback
	 spawn-world
	 deliver-event
	 transition-bind
	 sequence-transitions
	 clean-actions
	 routing-implementation)

;; A PID is a number uniquely identifying a Process within a World.
;; Note that PIDs are only meaningful within the context of their
;; World: they are not global Process identifiers.

;; TODO: support +Inf.0 as a level number

;; An Event is a communication from a World to a Process contained
;; within it. One of
;;  - (routing-update Gestalt), description of change in the sender's interests/subscriptions
;;  - (message Any Nat Boolean), a (multicast, in general) message sent by an actor
;; A message's (feedback?) field is #f when it is a message
;; originating from an advertiser/publisher and terminating with a
;; subscriber, and #t in the opposite case.
(struct routing-update (gestalt) #:prefab)
(struct message (body meta-level feedback?) #:prefab)

;; An Action is a communication from a Process to its containing
;; World, instructing the World to take some action on the Process's
;; behalf. One of
;;  - an Event: change in the Process's interests, or message from the Process
;;  - (spawn (Constreeof Action) Process): instruction to spawn a new process as described
;;  - (quit): instruction to terminate the sending process
(struct quit () #:prefab)
(struct spawn (boot-proc process) #:prefab)

;; A PendingEvent is a description of a set of Events to be
;; communicated to a World's Processes. In naïve implementations of
;; NC, there is no distinction between Events and PendingEvents; here,
;; we must ensure that the buffering delay doesn't affect the Gestalts
;; communicated in routing-update Events, so a special record is used
;; to capture the appropriate Gestalt environment.
;;  - (pending-routing-update Gestalt Gestalt (Option PID))
(struct pending-routing-update (aggregate affected-subgestalt known-target) #:prefab)

;; A Process (a.k.a. Actor) describes a single actor in a World.
;;  - (process Gestalt Behavior Any)
;; The Gestalt describes the current interests of the Process: either
;; those it was spawned with, or the most recent interests from a
;; routing-update Action.
(struct process (gestalt behavior state) #:transparent)

;; A World (a.k.a Configuration) is the state of an actor representing
;; a group of communicating Processes. The term is also used from time
;; to time to denote the actor having a World as its state and
;; world-handle-event as its Behavior.
(struct world (next-pid			;; PID, for next-spawned process
	       pending-event-queue	;; (Queueof PendingEvent)
	       runnable-pids		;; (Setof PID), non-inert processes
	       partial-gestalt		;; Gestalt, from local processes only; maps to PID
	       full-gestalt		;; Gestalt, union of partial- and downward-gestalts
	       process-table		;; (HashTable PID Process)
	       downward-gestalt		;; Gestalt, representing interests of outside world
	       process-actions		;; (Queueof (Pairof PID Action))
	       ) #:transparent)

;; A Behavior is a ((Option Event) Any -> Transition): a function
;; mapping an Event (or, in the #f case, a poll signal) and a
;; Process's current state to a Transition.
;;
;; A Transition is either
;;  - #f, a signal from a Process that it is inert and need not be
;;        scheduled until some Event relevant to it arrives; or,
;;  - a (transition Any (Constreeof Action)), a new Process state to
;;        be held by its World and a sequence of Actions for the World
;;        to take on the transitioning Process's behalf.
(struct transition (state actions) #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol and utilities

;; sub : Pattern [#:meta-level Nat] [#:level Nat] -> Gestalt
;; pub : Pattern [#:meta-level Nat] [#:level Nat] -> Gestalt
;;
;; Construct atomic Gestalts representing subscriptions/advertisements
;; matching the given pattern, at the given meta-level and level.
;; These are frequently used in combination with gestalt-union when
;; building spawn and routing-update Actions.
(define (sub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt #f p l ml))
(define (pub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt #t p l ml))

;; Gestalt Any -> Boolean
;; True iff m falls within the set of messages represented by the Gestalt.
(define (gestalt-accepts? g m)
  (match-define (message b ml f?) m)
  (not (set-empty? (gestalt-match-value g b ml f?))))

;; (Option Event) Gestalt -> (Option Event)
;; Returns a filtered version of e, narrowed to the perspective of g-filter.
(define (filter-event e g-filter)
  (match e
    [#f #f]
    [(routing-update g) (routing-update (gestalt-filter g g-filter))]
    [(? message? m) (and (gestalt-accepts? g-filter m) m)]))

;; Behavior Any [Gestalt] -> Action
;; Constructs a spawn Action for a new process with the given behavior
;; and state. If a Gestalt is supplied, the new process will begin its
;; existence with the corresponding subscriptions/advertisements/
;; conversational-responsibilities.
(define (make-spawn #:boot [boot-proc (lambda (state) (transition state '()))]
		    behavior
		    state
		    [gestalt (gestalt-empty)])
  (spawn boot-proc
	 (process gestalt behavior state)))

;; send : Any [#:meta-level Nat] -> Action
;; feedback : Any [#:meta-level Nat] -> Action
;;
;; Each constructs an Action that will deliver a body to peers at the
;; given meta-level. (send) constructs messages that will be delivered
;; to subscribers; (feedback), to advertisers.
(define (send body #:meta-level [ml 0]) (message body ml #f))
(define (feedback body #:meta-level [ml 0]) (message body ml #t))

;; Action* -> Action
;; Constructs an action which causes the creation of a new World
;; Process. The given actions will be taken by a primordial process
;; running in the context of the new World.
(define (spawn-world . boot-actions)
  (make-spawn world-handle-event
	      (enqueue-actions (world 0
				      (make-queue)
				      (set)
				      (gestalt-empty)
				      (gestalt-empty)
				      (hash)
				      (gestalt-empty)
				      (make-queue))
			       -1
			       (clean-actions boot-actions))))

;; Any -> Boolean; type predicates for Event and Action respectively.
(define (event? x) (or (routing-update? x) (message? x)))
(define (action? x) (or (event? x) (spawn? x) (quit? x)))

;; (Any -> Transition) Transition -> Transition
;; A kind of monad-ish bind operator: threads the state in t0 through
;; k, appending the action sequence from t0 with that from the result
;; of calling k.
;; TODO: sort out exactly how #f should propagate here
(define (transition-bind k t0)
  (match-define (transition state0 actions0) t0)
  (match (k state0)
    [#f t0]
    [(transition state1 actions1) (transition state1 (cons actions0 actions1))]))

;; Transition (Any -> Transition)* -> Transition
;; Each step is a function from state to Transition. The state in t0
;; is threaded through the steps; the action sequences are appended.
(define (sequence-transitions t0 . steps)
  (foldl transition-bind t0 steps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Trigger guards

;; TriggerGuards wrap process Behavior and state, only passing through
;; routing-update Events to their contained process behavior/state if
;; there has been a change. All other Events go straight through.
;;
;;  - (trigger-guard Gestalt Behavior Any)
;;
;; The structural similarity to Processes is meaningful: a Process
;; describes the current interests of the Process, as well as its
;; behavior. A TriggerGuard describes the current interests of the
;; Process's *environment*, and doesn't bother passing on a
;; routing-update unless the change is non-zero.
(struct trigger-guard (gestalt handler state) #:transparent)

;; Behavior :> (Option Event) TriggerGuard -> Transition
;; Inspects the given event: if it is a routing update, the contained
;; Gestalt is compared to the TriggerGuard's record of the previous
;; Gestalt from the environment, and only if it is different is it
;; passed on.
(define (trigger-guard-handle e s0)
  (match-define (trigger-guard old-gestalt handler old-state) s0)
  (define (deliver s)
    (match (ensure-transition (handler e old-state))
      [#f
       (if (eq? s s0) #f (transition s '()))]
      [(transition new-state actions)
       (transition (struct-copy trigger-guard s [state new-state]) actions)]))
  (match e
    [(routing-update new-gestalt)
     (if (equal? new-gestalt old-gestalt)
	 #f
	 (deliver (struct-copy trigger-guard s0 [gestalt new-gestalt])))]
    [_ (deliver s0)]))

;; Process -> Process
;; Wraps a Process in a TriggerGuard.
(define (trigger-guard-process p)
  (match-define (process _ b s) p)
  (struct-copy process p [behavior trigger-guard-handle] [state (trigger-guard #f b s)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; World implementation

;; Each time a world is handed an event from its environment, it:
;;  1. dispatches PendingEvents
;;      a. removing them one-at-a-time from the queue
;;      b. converting them to Events and dispatching them to processes
;;      c. updating process states and accumulating Actions in the queue
;;      d. any process that returned non-#f is considered "non-idle" for step 3.
;;  2. performs Actions
;;      a. removing them one-at-a-time from the queue
;;      b. interpreting them
;;      c. updating World state and accumulating PendingEvents in the queue
;;  3. steps non-idle processes
;;      a. runs through the runnable-pids set of processes accumulated in 1d. above
;;      b. any process that returned non-#f is put in the "non-idle" set for next time
;;  4. yields updated World state and world Actions to the environment.
;;
;; Note that routing-update Actions are queued as
;; pending-routing-update structures in order to preserve and
;; communicate transient Gestalt states to Processes. In addition, the
;; known-target field of a pending-routing-update structure is used to
;; provide NC's initial Gestalt signal to a newly-spawned process.
;;
;; TODO: should step 3 occur before step 1?

;; World PID (Listof Action) -> World
;; Stores actions taken by PID for later interpretation.
(define (enqueue-actions w pid actions)
  (struct-copy world w
    [process-actions (queue-append-list (world-process-actions w)
					(for/list [(a actions)] (cons pid a)))]))

;; World -> Boolean
;; True if the World has no further reductions it can take.
;;
;; The code is written to maintain the runnable-pids set carefully, to
;; ensure we can locally decide whether we're inert or not without
;; having to search the whole deep process tree.
(define (inert? w)
  (and (queue-empty? (world-pending-event-queue w))
       (queue-empty? (world-process-actions w))
       (set-empty? (world-runnable-pids w))))

;; Event PID Process World -> World
;; Delivers the event to the process, then applies the resulting
;; transition, updating the world.
(define (step-process e pid p w)
  (apply-transition pid (deliver-event e pid p) w))

;; Event PID Process -> Transition
;; Delivers the event to the process.
(define (deliver-event e pid p)
  (invoke-process (process-behavior p) e pid p))

;; (Any -> (Option Transition)) PID Process -> (Option Transition)
;; Calls f in the context of the given process, catching exceptions.
(define (invoke-process f e pid p)
  (define-values (maybe-exn t)
    (call-in-trace-context
     pid
     (lambda ()
       (with-handlers ([(lambda (exn) #t)
			(lambda (exn) (values exn (transition (process-state p) (list (quit)))))])
	 (values
	  #f
	  (clean-transition
	   (ensure-transition (with-continuation-mark 'minimart-process pid (f e (process-state p))))))))))
  (trace-process-step e pid p maybe-exn t)
  t)

;; Any -> (Option Transition)
;; If its argument is non-#f, non-transition, raises an exception.
(define (ensure-transition v)
  (if (or (not v) (transition? v))
      v
      (raise (exn:fail:contract (format "Expected transition (or #f); got ~v" v)
				(current-continuation-marks)))))

;; (Option Transition) -> (Option Transition)
;; Filters and flattens action constree in argument.
(define (clean-transition t)
  (and t (transition (transition-state t) (clean-actions (transition-actions t)))))

;; (Constreeof Any) -> (Listof Action)
;; Filters and flattens its argument to a list of actions.
(define (clean-actions actions)
  (filter action? (flatten actions)))

;; World PID -> World
;; Marks the given PID as not-provably-inert.
(define (mark-pid-runnable w pid)
  (struct-copy world w [runnable-pids (set-add (world-runnable-pids w) pid)]))

;; PID Transition World -> World
;; Examines the given Transition, updating PID's Process's state and
;; enqueueing Actions for later interpretation. When the Transition is
;; non-#f, PID's Process may wish to take further internal reductions,
;; so we mark it as runnable.
(define (apply-transition pid t w)
  (match t
    [#f w]
    [(transition new-state new-actions)
     (let* ((w (transform-process pid w (lambda (p) (struct-copy process p [state new-state])))))
       (enqueue-actions (mark-pid-runnable w pid) pid new-actions))]))

;; PendingEvent World -> World
;; Enqueue a PendingEvent for later interpretation and dispatch.
(define (enqueue-pending-event e w)
  (struct-copy world w [pending-event-queue (enqueue (world-pending-event-queue w) e)]))

;; World -> Transition
;; Examines all queued actions, interpreting them, updating World
;; state, and possibly causing the World to send Actions for
;; interpretation to its own containing World in turn.
(define (perform-actions w)
  (for/fold ([t (transition (struct-copy world w [process-actions (make-queue)]) '())])
      ((entry (in-list (queue->list (world-process-actions w)))))
    (match-define (cons pid a) entry)
    (define t1 (transition-bind (perform-action pid a) t))
    (trace-internal-step pid a (transition-state t) t1)
    t1))

;; World -> Transition
;; Interprets queued PendingEvents, delivering resulting Events to Processes.
(define (dispatch-pending-events w)
  (transition (for/fold ([w (struct-copy world w [pending-event-queue (make-queue)])])
		  ((e (in-list (queue->list (world-pending-event-queue w)))))
		(dispatch-pending-event e w))
              '()))

;; PID World (Process -> Process) -> World
;; Extracts a Process by PID, maps fp over it, and stores the result back into the table.
(define (transform-process pid w fp)
  (define pt (world-process-table w))
  (match (hash-ref pt pid)
    [#f w]
    [p (struct-copy world w [process-table (hash-set pt pid (fp p))])]))

;; World -> World
;; Updates the World's cached copy of the union of its partial- and downward-gestalts.
(define (update-full-gestalt w)
  (define new-full-gestalt (gestalt-union (world-partial-gestalt w) (world-downward-gestalt w)))
  (struct-copy world w [full-gestalt new-full-gestalt]))

;; World Gestalt (Option PID) -> World
;; Constructs and enqueues a PendingEvent describing a change to the
;; World's gestalt falling within the relevant-gestalt *subset* of it.
(define (issue-local-routing-update w relevant-gestalt known-target)
  (enqueue-pending-event (pending-routing-update (world-full-gestalt w)
						 relevant-gestalt
						 known-target)
			 w))

;; World Gestalt (Option PID) -> Transition
;; Communicates a change in World's gestalt falling within the
;; relevant-gestalt *subset* of it both to local Processes and to the
;; World's own containing World.
(define (issue-routing-update w relevant-gestalt known-target)
  (transition (issue-local-routing-update w relevant-gestalt known-target)
              (routing-update (drop-gestalt (world-partial-gestalt w)))))

;; World Gestalt Gestalt (Option PID) -> Transition
;; Communicates a change in the World gestalt corresponding to a
;; change in a single Process's gestalt. The old-gestalt is what the
;; Process used to be interested in; new-gestalt is its new interests.
(define (apply-and-issue-routing-update w old-gestalt new-gestalt known-target)
  (define new-partial
    (gestalt-union (gestalt-subtract (world-partial-gestalt w) old-gestalt) new-gestalt))
  (issue-routing-update (update-full-gestalt (struct-copy world w [partial-gestalt new-partial]))
			(gestalt-union old-gestalt new-gestalt)
			known-target))

;; PID Action -> World -> Transition
;; Interprets a single Action performed by PID, updating World state
;; and possibly causing the World to take externally-visible Actions
;; as a result.
(define ((perform-action pid a) w)
  (match a
    [(spawn boot-proc new-p)
     (let* ((new-pid (world-next-pid w))
	    (initial-t (invoke-process (lambda (e s) (boot-proc s)) '#:boot new-pid new-p))
	    (initial-actions (if initial-t (transition-actions initial-t) '()))
	    (new-p (if initial-t (struct-copy process new-p [state (transition-state initial-t)]) new-p))
	    (new-p (trigger-guard-process new-p))
	    (new-gestalt (label-gestalt (process-gestalt new-p) new-pid))
	    (new-p (struct-copy process new-p [gestalt new-gestalt]))
	    (w (struct-copy world w
		 [next-pid (+ new-pid 1)]
		 [process-table (hash-set (world-process-table w) new-pid new-p)]))
	    (w (enqueue-actions w new-pid initial-actions)))
       (apply-and-issue-routing-update w (gestalt-empty) new-gestalt new-pid))]
    [(quit)
     (define pt (world-process-table w))
     (define p (hash-ref pt pid (lambda () #f)))
     (if p
	 (let* ((w (struct-copy world w [process-table (hash-remove pt pid)])))
	   (apply-and-issue-routing-update w (process-gestalt p) (gestalt-empty) #f))
	 (transition w '()))]
    [(routing-update gestalt)
     (define pt (world-process-table w))
     (define p (hash-ref pt pid (lambda () #f)))
     (if p
	 (let* ((old-gestalt (process-gestalt p))
		(new-gestalt (label-gestalt gestalt pid))
		(new-p (struct-copy process p [gestalt new-gestalt]))
		(w (struct-copy world w [process-table (hash-set pt pid new-p)])))
	   (apply-and-issue-routing-update w old-gestalt new-gestalt #f))
	 (transition w '()))]
    [(message body meta-level feedback?)
     (if (zero? meta-level)
	 (transition (enqueue-pending-event a w) '())
	 (transition w (message body (- meta-level 1) feedback?)))]))

;; PendingEvent World -> World
;; Interprets a PendingEvent, delivering the resulting Event(s) to Processes.
(define (dispatch-pending-event e w)
  (match e
    [(message body meta-level feedback?)
     (define pids (gestalt-match-value (world-partial-gestalt w) body meta-level feedback?))
     (define pt (world-process-table w))
     (for/fold ([w w]) [(pid (in-list (tset->list pids)))] (step-process e pid (hash-ref pt pid) w))]
    [(pending-routing-update g affected-subgestalt known-target)
     (define affected-pids (gestalt-match affected-subgestalt g))
     (define pt (world-process-table w))
     (for/fold ([w w])
	 [(pid (in-list (tset->list (if known-target (tset-add affected-pids known-target) affected-pids))))]
       (match (hash-ref pt pid (lambda () #f))
	 [#f w]
	 [p (step-process (routing-update (gestalt-filter g (process-gestalt p))) pid p w)]))]))

;; World -> Transition
;; Polls the non-provably-inert processes identified by the
;; runnable-pids set (by sending them #f instead of an Event).
;;
;; N.B.: We also effectively compute whether this entire World is
;; inert here.
;;
;; This is roughly the "schedule" rule of the Network Calculus.
(define (step-children w)
  (define runnable-pids (world-runnable-pids w))
  (if (set-empty? runnable-pids)
      #f ;; world is inert.
      (transition (for/fold ([w (struct-copy world w [runnable-pids (set)])])
		      [(pid (in-set runnable-pids))]
		    (define p (hash-ref (world-process-table w) pid (lambda () #f)))
		    (if (not p) w (step-process #f pid p w)))
		  '()))) ;; world needs another check to see if more can happen.

;; Behavior :> (Option Event) World -> Transition
;; World's behavior function. Lifts and dispatches an incoming event
;; to contained Processes.
(define (world-handle-event e w)
  (if (or e (not (inert? w)))
      (sequence-transitions (transition (inject-event e w) '())
			    dispatch-pending-events
			    perform-actions
			    (lambda (w) (or (step-children w) (transition w '()))))
      (step-children w)))

;; Event World -> World
;; Translates an event from the World's container into PendingEvents
;; suitable for its own contained Processes.
(define (inject-event e w)
  (match e
    [#f w]
    [(routing-update g)
     (define old-downward (world-downward-gestalt w))
     (define new-downward (lift-gestalt (label-gestalt g 'out)))
     (issue-local-routing-update (update-full-gestalt
				  (struct-copy world w [downward-gestalt new-downward]))
				 (gestalt-union old-downward new-downward)
				 #f)]
    [(message body meta-level feedback?)
     (enqueue-pending-event (message body (+ meta-level 1) feedback?) w)]))

;; Symbol
;; Describes the routing implementation, for use in profiling, debugging etc.
(define routing-implementation 'fastrouting)
