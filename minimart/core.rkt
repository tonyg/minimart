#lang racket/base

(require racket/match)
(require racket/list)
(require "pattern.rkt")
(require "functional-queue.rkt")
(require (only-in web-server/private/util exn->string))

(require rackunit) ;; TODO: split out

(provide (struct-out route)
	 (struct-out routing-update)
	 (struct-out message)
	 (struct-out quit)
	 (struct-out process)
	 (struct-out transition)
	 ? ;; imported from pattern.rkt
	 wildcard?
	 sub
	 pub
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

;; A Gestalt is a (gestalt (Listof (Vectorof (Pairof Matcher
;; Matcher)))), representing the total interests of a process or group
;; of processes. The outer list has a present entry for each active
;; metalevel, starting with metalevel 0 in the car. The vectors each
;; have an entry for each active observer level at their metalevel.
;; The innermost pairs have cars holding matchers representing active
;; subscriptions, and cdrs representing active advertisements.
;;
;;    "... a few standardised subsystems, identical from citizen to
;;     citizen. Two of these were channels for incoming data — one for
;;     gestalt, and one for linear, the two primary modalities of all
;;     Konishi citizens, distant descendants of vision and hearing."
;;      -- Greg Egan, "Diaspora"
;;         http://gregegan.customer.netspace.net.au/DIASPORA/01/Orphanogenesis.html
;;
(struct gestalt (metalevels) #:prefab)

;; Events
(struct routing-update (gestalt) #:prefab)
(struct message (body meta-level feedback?) #:prefab)

;; Actions (in addition to Events)
;; (spawn is just process)
(struct quit () #:prefab)

;; Actors and Configurations
(struct process (gestalt behavior state) #:transparent)
(struct world (next-pid event-queue process-table downward-gestalt process-actions) #:transparent)

;; Behavior : maybe event * state -> transition
(struct transition (state actions) #:transparent)

;; TODO: Reintroduce "trigger-guard" from the naive implementation
;; perhaps. "Process table maps to these; idea is to avoid redundant
;; signalling of routing-updates where possible"

(define (drop-gestalt g)
  (match-define (gestalt metalevels) g)
  (gestalt (if (null? metalevels) '() (cdr metalevels))))

(define (lift-gestalt g)
  (gestalt (cons '#() (gestalt-metalevels g))))

(define (simple-gestalt subs advs level metalevel)
  (define leaf (cons subs advs))
  (define vec (make-vector (+ level 1) (cons #f #f)))
  (vector-set! vec level leaf)
  (let loop ((n metalevel) (acc (list vec)))
    (if (zero? n)
	(gestalt acc)
	(loop (- n 1) (cons '#() acc)))))

(define (gestalt-empty) (gestalt '()))

(define (gestalt-union g1 g2)
  (define (zu sa1 sa2)
    (cons (matcher-union (car sa1) (car sa2))
	  (matcher-union (cdr sa1) (cdr sa2))))
  (define (yu ls1 ls2)
    (define vl1 (vector-length ls1))
    (define vl2 (vector-length ls2))
    (define one-bigger? (> vl1 vl2))
    (define maxlen (max vl1 vl2))
    (define minlen (min vl1 vl2))
    (define result (make-vector maxlen #f))
    (for ((i (in-range 0 minlen)))
      (vector-set! result i (zu (vector-ref ls1 i) (vector-ref ls2 i))))
    (for ((i (in-range minlen maxlen)))
      (vector-set! result i (vector-ref (if one-bigger? vl1 vl2) i)))
    result)
  (define (xu mls1 mls2)
    (match* (mls1 mls2)
      [('() mls) mls]
      [(mls '()) mls]
      [((cons m1 mls1) (cons m2 mls2)) (cons (yu m1 m2) (xu mls1 mls2))]))
  (gestalt (xu (gestalt-metalevels g1)
	       (gestalt-metalevels g2))))

(check-equal? (simple-gestalt 'a 'b 0 0)
	      (gestalt (list (vector (cons 'a 'b)))))
(check-equal? (simple-gestalt 'a 'b 2 2)
	      (gestalt (list '#() '#() (vector (cons #f #f)
					       (cons #f #f)
					       (cons 'a 'b)))))

(define (sub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt (pattern->matcher #t p) #f l ml))
(define (pub p #:meta-level [ml 0] #:level [l 0]) (simple-gestalt #f (pattern->matcher #t p) l ml))

(define (spawn behavior state [gestalt (gestalt-empty)]) (process gestalt behavior state))
(define (send body #:meta-level [ml 0]) (message body ml #f))
(define (feedback body #:meta-level [ml 0]) (message body ml #t))

(define (spawn-world . boot-actions)
  (spawn world-handle-event
	 (enqueue-actions (world 0 (make-queue) (hash) (gestalt-empty) (make-queue))
			  -1
			  boot-actions)))

(define (event? x) (or (routing-update? x) (message? x)))
(define (action? x) (or (event? x) (process? x) (quit? x)))

(define (enqueue-actions w pid actions)
  (struct-copy world w
    [process-actions (queue-append-list (world-process-actions w)
					(filter-map (lambda (a) (and (action? a) (cons pid a)))
						    (flatten actions)))]))

(define (quiescent? w)
  (and (queue-empty? (world-event-queue w))
       (queue-empty? (world-process-actions w))))

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
	[#f #f]
	[(? transition? t) t]
	[x
	 (log-error "Process ~a returned non-#f, non-transition: ~v" pid x)
	 (transition (process-state p) (list (quit)))]))))

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
       (enqueue-actions w pid new-actions))]))

(define (transition-bind k t0)
  (match-define (transition state0 actions0) t0)
  (match-define (transition state1 actions1) (k state0))
  (transition state1 (cons actions0 actions1)))

(define (sequence-transitions t0 . steps)
  (foldl transition-bind t0 steps))

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
  (define pt (world-process-actions w))
  (match (hash-ref pt pid)
    [#f w]
    [p (struct-copy world w [process-table (hash-set pt pid (fp p))])]))

(define (enqueue-event e w)
  (struct-copy world w [event-queue (enqueue (world-event-queue w) e)]))

(define ((perform-action pid a) w)
  (match a
    [(? process? new-p)
     (let* ((new-pid (world-next-pid w))
	    (w (struct-copy world w [next-pid (+ new-pid 1)]))
	    (w (struct-copy world w [process-table
				     (hash-set (world-process-table w) new-pid new-p)])))
       (log-info "Spawned process ~a ~v ~v" new-pid (process-behavior new-p) (process-state new-p))
       (issue-routing-update w))]
    [(quit)
     (when (hash-has-key? (world-process-table w) pid) (log-info "Process ~a terminating" pid))
     (let* ((w (struct-copy world w [process-table (hash-remove (world-process-table w) pid)])))
       (issue-routing-update w))]
    [(routing-update gestalt)
     (let* ((w (transform-process pid w
				  (lambda (p) (struct-copy process p [gestalt gestalt])))))
       (issue-routing-update w))]
    [(message body meta-level feedback?)
     (if (zero? meta-level)
	 (transition (enqueue-event a w) '())
	 (transition w (message body (- meta-level 1) feedback?)))]))

(define (issue-local-routing-update w)
  (enqueue-event (routing-update (aggregate-routes (world-downward-routes w) w)) w))

(define (issue-routing-update w)
  (transition (issue-local-routing-update w)
              (routing-update (drop-routes (aggregate-routes '() w)))))

(define (dispatch-event e w)
  ...)

;; TODO: need explicit indication from a transitioning child as to
;; whether it is inert or not. If not, it should be explicitly
;; scheduled for the next round. The current system of just asking
;; everyone doesn't scale.
;;
;; This is the "schedule" rule of the calculus.
;;
(define (step-children w)
  (let-values (((w step-taken?)
		(for/fold ([w w] [step-taken? #f]) (((pid g) (in-hash (world-process-table w))))
		  (match-define (trigger-guard p _) g)
		  (define t (deliver-event #f pid p))
		  (values (apply-transition pid t w)
			  (or step-taken? (transition? t))))))
    (and step-taken? (transition w '()))))

(define (world-handle-event e w)
  (if (or e (not (quiescent? w)))
      (sequence-transitions (transition (inject-event e w) '())
			    dispatch-events
			    perform-actions
			    (lambda (w) (or (step-children w) (transition w '()))))
      (step-children w)))

(define (inject-event e w)
  (match e
    [#f w]
    [(routing-update routes)
     (issue-local-routing-update (struct-copy world w [downward-routes (lift-routes routes)]))]
    [(message body meta-level feedback?)
     (enqueue-event (message body (+ meta-level 1) feedback?) w)]))
