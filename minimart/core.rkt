#lang racket/base

(require racket/match)
(require racket/list)
(require "pattern.rkt")
(require "functional-queue.rkt")
(require (only-in web-server/private/util exn->string))

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
	 co-route
	 route-accepts?
	 intersect-routes
	 spawn-world
	 deliver-event
	 transition-bind
	 sequence-transitions)

(struct route (subscription? pattern meta-level level) #:prefab)

;; Events
(struct routing-update (routes) #:prefab)
(struct message (body meta-level feedback?) #:prefab)

;; Actions (in addition to Events)
;; (spawn is just process)
(struct quit () #:prefab)

;; Actors and Configurations
(struct process (routes behavior state) #:transparent)
(struct world (next-pid event-queue process-table downward-routes process-actions) #:transparent)

;; Behavior : maybe event * state -> transition
(struct transition (state actions) #:transparent)

(define (drop-route r)
  (match-define (route s? p ml l) r)
  (and (positive? ml) (route s? p (- ml 1) l)))

(define (lift-route r)
  (match-define (route s? p ml l) r)
  (route s? p (+ ml 1) l))

(define (sub p #:meta-level [ml 0] #:level [l 0]) (route #t p ml l))
(define (pub p #:meta-level [ml 0] #:level [l 0]) (route #f p ml l))

(define (spawn behavior state [initial-routes '()]) (process initial-routes behavior state))
(define (send body #:meta-level [ml 0]) (message body ml #f))
(define (feedback body #:meta-level [ml 0]) (message body ml #t))

(define (drop-routes rs) (filter-map drop-route rs))
(define (lift-routes rs) (map lift-route rs))

(define (co-route r #:level [level-override #f])
  (match-define (route sub? pat ml l) r)
  (route (not sub?) pat ml (or level-override l)))

(define (route-accepts? r m)
  (and (= (message-meta-level m) (route-meta-level r))
       (equal? (message-feedback? m) (not (route-subscription? r)))
       (intersect? (message-body m) (route-pattern r))))

(define (intersect-routes rs1 rs2)
  (let loop1 ((rs1 rs1)
	      (acc '()))
    (match rs1
      ['() (reverse acc)]
      [(cons r1 rs1)
       (let loop2 ((rs2 rs2)
		   (acc acc))
	 (match rs2
	   ['() (loop1 rs1 acc)]
	   [(cons r2 rs2)
	    (if (and (equal? (route-subscription? r1) (not (route-subscription? r2)))
		     (= (route-meta-level r1) (route-meta-level r2))
		     (< (route-level r1) (route-level r2)))
		(intersect (route-pattern r1) (route-pattern r2)
			   (lambda (rr) (loop2 rs2 (cons (struct-copy route r1 [pattern rr]) acc)))
			   (lambda () (loop2 rs2 acc)))
		(loop2 rs2 acc))]))])))

(define (filter-event e rs)
  (match e
    [(routing-update e-rs)
     (routing-update (intersect-routes e-rs rs))]
    [(? message? m)
     (if (ormap (lambda (r) (route-accepts? r m)) rs) e #f)]))

(define (spawn-world . boot-actions)
  (spawn world-handle-event
	 (enqueue-actions (world 0 (make-queue) (hash) '() (make-queue))
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
  (with-handlers ([(lambda (exn) #t)
		   (lambda (exn)
		     (log-error "Process ~a died with exception:\n~a" pid (exn->string exn))
		     (transition (process-state p) (list (quit))))])
    (match ((process-behavior p) e (process-state p))
      [#f #f]
      [(? transition? t) t]
      [x
       (log-error "Process ~a returned non-#f, non-transition: ~v" pid x)
       (transition (process-state p) (list (quit)))])))

(define (apply-transition pid t w)
  (match t
    [#f w]
    [(transition new-state new-actions)
     (let* ((w (transform-process pid w (lambda (p) (struct-copy process p [state new-state])))))
       (enqueue-actions w pid new-actions))]))

(define (step-children w)
  (let-values (((w step-taken?)
		(for/fold ([w w] [step-taken? #f]) (((pid p) (in-hash (world-process-table w))))
		  (define t (deliver-event #f pid p))
		  (values (apply-transition pid t w)
			  (or step-taken? (transition? t))))))
    (and step-taken? (transition w '()))))

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

(define (transform-process pid w f)
  (define p (hash-ref (world-process-table w) pid))
  (if p
      (struct-copy world w [process-table (hash-set (world-process-table w) pid (f p))])
      w))

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
    [(routing-update routes)
     (let* ((w (transform-process pid w (lambda (p) (struct-copy process p [routes routes])))))
       (issue-routing-update w))]
    [(message body meta-level feedback?)
     (if (zero? meta-level)
	 (transition (enqueue-event a w) '())
	 (transition w (message body (- meta-level 1) feedback?)))]))

(define (aggregate-routes base w)
  (apply append base (for/list ((p (in-hash-values (world-process-table w)))) (process-routes p))))

(define (issue-local-routing-update w)
  (enqueue-event (routing-update (aggregate-routes (world-downward-routes w) w)) w))

(define (issue-routing-update w)
  (transition (issue-local-routing-update w)
              (routing-update (drop-routes (aggregate-routes '() w)))))

(define (dispatch-event e w)
  (for/fold ([w w]) (((pid p) (in-hash (world-process-table w))))
    (define e1 (filter-event e (process-routes p)))
    (if e1
	(apply-transition pid (deliver-event e1 pid p) w)
	w)))

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
