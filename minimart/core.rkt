#lang racket/base

(require racket/set)
(require racket/match)
(require racket/list)
(require "route.rkt")
(require "gestalt.rkt")
(require "functional-queue.rkt")
(require (only-in web-server/private/util exn->string))

(provide (struct-out routing-update)
	 (struct-out message)
	 (struct-out quit)
	 (struct-out process)
	 (struct-out transition)

	 ;; imported from route.rkt:
	 ?
	 wildcard?
	 ?!
	 capture?

	 sub
	 pub
	 gestalt-union
	 gestalt-ref
	 compile-gestalt-projection
	 gestalt-project
	 gestalt-project->finite-set

	 spawn
	 send
	 feedback
	 spawn-world
	 deliver-event
	 transition-bind
	 sequence-transitions
	 log-events-and-actions?)

(define pid-stack (make-parameter '()))
(define log-events-and-actions? (make-parameter #f))

;; Events
(struct routing-update (gestalt) #:prefab)
(struct message (body meta-level feedback?) #:prefab)

;; Actions (in addition to Events)
;; (spawn is just process)
(struct quit () #:prefab)

;; Actors and Configurations
(struct process (gestalt behavior state) #:transparent)
(struct world (next-pid			;; Natural, PID for next-spawned process
	       event-queue		;; Queue of Event
	       runnable-pids		;; Set of PIDs
	       aggregate-gestalt	;; Gestalt mapping to PID
	       process-table		;; Hash from PID to Process
	       downward-gestalt		;; GestaltSet representing interests of outside world
	       process-actions		;; Queue of (cons PID Action)
	       ) #:transparent)

;; Behavior : maybe event * state -> transition
(struct transition (state actions) #:transparent)

;; TODO: Reintroduce "trigger-guard" from the naive implementation
;; perhaps. "Process table maps to these; idea is to avoid redundant
;; signalling of routing-updates where possible"

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol and utilities

(define (sub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt (pattern->matcher #t p) #f l ml))
(define (pub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt #f (pattern->matcher #t p) l ml))

(define (spawn behavior state [gestalt (gestalt-empty)]) (process gestalt behavior state))
(define (send body #:meta-level [ml 0]) (message body ml #f))
(define (feedback body #:meta-level [ml 0]) (message body ml #t))

(define (spawn-world . boot-actions)
  (spawn world-handle-event
	 (enqueue-actions (world 0
				 (make-queue)
				 (set)
				 (gestalt-empty)
				 (hash)
				 (gestalt-empty)
				 (make-queue))
			  -1
			  boot-actions)))

(define (event? x) (or (routing-update? x) (message? x)))
(define (action? x) (or (event? x) (process? x) (quit? x)))

(define (transition-bind k t0)
  (match-define (transition state0 actions0) t0)
  (match-define (transition state1 actions1) (k state0))
  (transition state1 (cons actions0 actions1)))

(define (sequence-transitions t0 . steps)
  (foldl transition-bind t0 steps))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; World implementation

(define (enqueue-actions w pid actions)
  (struct-copy world w
    [process-actions (queue-append-list (world-process-actions w)
					(filter-map (lambda (a) (and (action? a) (cons pid a)))
						    (flatten actions)))]))

;; The code is written to maintain the runnable-pids set carefully, to
;; ensure we can locally decide whether we're inert or not without
;; having to search the whole deep process tree.
(define (inert? w)
  (and (queue-empty? (world-event-queue w))
       (queue-empty? (world-process-actions w))
       (set-empty? (world-runnable-pids w))))

(define (deliver-event e pid p)
  (parameterize ((pid-stack (cons pid (pid-stack))))
    (when (and (log-events-and-actions?) e)
      (log-info "~a: ~v --> ~v ~v"
		(reverse (pid-stack))
		e
		(process-behavior p)
		(if (world? (process-state p))
		    "#<world>"
		    (process-state p))))
    (with-handlers ([(lambda (exn) #t)
		     (lambda (exn)
		       (log-error "Process ~a died with exception:\n~a" pid (exn->string exn))
		       (transition (process-state p) (list (quit))))])
      (match (with-continuation-mark 'minimart-process
				     pid ;; TODO: debug-name, other user annotation
				     ((process-behavior p) e (process-state p)))
	[#f #f] ;; inert.
	[(? transition? t) t] ;; potentially runnable.
	[x
	 (log-error "Process ~a returned non-#f, non-transition: ~v" pid x)
	 (transition (process-state p) (list (quit)))]))))

(define (mark-pid-runnable w pid)
  (struct-copy world w [runnable-pids (set-add (world-runnable-pids w) pid)]))

(define (apply-transition pid t w)
  (match t
    [#f w]
    [(transition new-state new-actions)
     (let* ((w (transform-process pid w
				  (lambda (p)
				    (when (and (log-events-and-actions?)
					       (not (null? (flatten new-actions))))
				      (log-info "~a: ~v <-- ~v ~v"
						(reverse (cons pid (pid-stack)))
						new-actions
						(process-behavior p)
						(if (world? new-state)
						    "#<world>"
						    new-state)))
				    (struct-copy process p [state new-state])))))
       (enqueue-actions (mark-pid-runnable w pid) pid new-actions))]))

(define (enqueue-event e w)
  (struct-copy world w [event-queue (enqueue (world-event-queue w) e)]))

(define (perform-actions w)
  (for/fold ([t (transition (struct-copy world w [process-actions (make-queue)]) '())])
      ((entry (in-list (queue->list (world-process-actions w)))))
    (match-define (cons pid a) entry)
    (transition-bind (perform-action pid a) t)))

(define (dispatch-events w)
  (transition (for/fold ([w (struct-copy world w [event-queue (make-queue)])])
		  ((e (in-list (queue->list (world-event-queue w)))))
		(dispatch-event e w))
              '()))

(define (transform-process pid w fp)
  (define pt (world-process-table w))
  (match (hash-ref pt pid)
    [#f w]
    [p (struct-copy world w [process-table (hash-set pt pid (fp p))])]))

(define (update-aggregate-gestalt w pid old-g new-g)
  (struct-copy world w [aggregate-gestalt
			(gestalt-union (gestalt-combine-straight old-g
								 (world-aggregate-gestalt w)
								 (lambda (side x)
								   (case side
								     [(left-longer) '()]
								     [(right-longer) x]))
								 matcher-erase-path)
				       new-g)]))

(define (issue-local-routing-update w relevant-gestalt)
  (enqueue-event (routing-update relevant-gestalt) w))

(define (issue-routing-update w relevant-gestalt)
  (transition (issue-local-routing-update w relevant-gestalt)
              (routing-update (drop-gestalt (world-aggregate-gestalt w)))))

(define (apply-and-issue-routing-update w pid old-gestalt new-gestalt)
  (issue-routing-update (update-aggregate-gestalt w pid old-gestalt new-gestalt)
			(gestalt-union old-gestalt new-gestalt)))

(define ((perform-action pid a) w)
  (match a
    [(? process? new-p)
     (let* ((new-pid (world-next-pid w))
	    (new-gestalt (label-gestalt (process-gestalt new-p) new-pid))
	    (new-p (struct-copy process new-p [gestalt new-gestalt]))
	    (w (struct-copy world w
		 [next-pid (+ new-pid 1)]
		 [process-table (hash-set (world-process-table w) new-pid new-p)])))
       (log-info "Spawned process ~a ~v ~v" new-pid (process-behavior new-p) (process-state new-p))
       (apply-and-issue-routing-update w new-pid (gestalt-empty) new-gestalt))]
    [(quit)
     (define pt (world-process-table w))
     (define p (hash-ref pt pid (lambda () #f)))
     (if p
	 (let* ((w (struct-copy world w [process-table (hash-remove pt pid)])))
	   (log-info "Process ~a terminating" pid)
	   (apply-and-issue-routing-update w pid (process-gestalt p) (gestalt-empty)))
	 (transition w '()))]
    [(routing-update gestalt)
     (define pt (world-process-table w))
     (define p (hash-ref pt pid (lambda () #f)))
     (if p
	 (let* ((old-gestalt (process-gestalt p))
		(new-gestalt (label-gestalt gestalt pid))
		(new-p (struct-copy process p [gestalt new-gestalt]))
		(w (struct-copy world w [process-table (hash-set pt pid new-p)])))
	   (apply-and-issue-routing-update w pid old-gestalt new-gestalt))
	 (transition w '()))]
    [(message body meta-level feedback?)
     (if (zero? meta-level)
	 (transition (enqueue-event a w) '())
	 (transition w (message body (- meta-level 1) feedback?)))]))

;; NOTE: routing-update events arriving here carry descriptions of the
;; changed region of the aggregate, NOT the whole aggregate.
(define (dispatch-event e w)
  (match e
    [(message body meta-level feedback?)
     (define matcher (gestalt-ref (world-aggregate-gestalt w) meta-level 0 feedback?))
     (define pids (matcher-match-value matcher body))
     (define pt (world-process-table w))
     (for/fold ([w w]) [(pid (in-set pids))]
       (apply-transition pid (deliver-event e pid (hash-ref pt pid)) w))]
    [(routing-update affected-subgestalt)
     (define g (world-aggregate-gestalt w))
     (define-values (affected-pids uninteresting) (gestalt-match g affected-subgestalt))
     (define pt (world-process-table w))
     (for/fold ([w w]) [(pid (in-set affected-pids))]
       (define p (hash-ref pt pid))
       (define g1 (gestalt-filter g (process-gestalt p)))
       (apply-transition pid (deliver-event (routing-update g1) pid p) w))]))

;; This is roughly the "schedule" rule of the calculus.
(define (step-children w)
  (define runnable-pids (world-runnable-pids w))
  (if (set-empty? runnable-pids)
      #f ;; world is inert.
      (transition (for/fold ([w (struct-copy world w [runnable-pids (set)])])
		      [(pid (in-set runnable-pids))]
		    (define p (hash-ref (world-process-table w) pid))
		    (apply-transition pid (deliver-event #f pid p) w))
		  '()))) ;; world needs another check to see if more can happen.

(define (world-handle-event e w)
  (if (or e (not (inert? w)))
      (sequence-transitions (transition (inject-event e w) '())
			    dispatch-events
			    perform-actions
			    (lambda (w) (or (step-children w) (transition w '()))))
      (step-children w)))

(define (inject-event e w)
  (match e
    [#f w]
    [(routing-update g)
     (define old-downward (world-downward-gestalt w))
     (define new-downward (lift-gestalt (label-gestalt g 'out)))
     (issue-local-routing-update (update-aggregate-gestalt w 'out old-downward new-downward)
				 (gestalt-union old-downward new-downward))]
    [(message body meta-level feedback?)
     (enqueue-event (message body (+ meta-level 1) feedback?) w)]))
