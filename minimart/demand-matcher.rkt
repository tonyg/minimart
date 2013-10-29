#lang racket/base

(require racket/match)
(require "core.rkt")
(require "presence-detector.rkt")

(provide (except-out (struct-out demand-matcher) demand-matcher)
	 (rename-out [make-demand-matcher demand-matcher])
	 demand-matcher-update
	 spawn-demand-matcher)

(struct demand-matcher (demand-is-subscription?
			pattern
			meta-level
			demand-level
			supply-level
			increase-handler
			decrease-handler
			state)
	#:transparent)

(define (unexpected-supply-decrease r)
  (error 'demand-matcher "Unexpected decrease in supply for route ~a" r))

(define (default-decrease-handler removed state)
  (unexpected-supply-decrease removed))

(define (make-demand-matcher demand-is-subscription?
			     pattern
			     meta-level
			     demand-level
			     supply-level
			     increase-handler
			     [decrease-handler default-decrease-handler])
  (demand-matcher demand-is-subscription?
		  pattern
		  meta-level
		  demand-level
		  supply-level
		  increase-handler
		  decrease-handler
		  (presence-detector)))

(define (compute-detector demand? d)
  (route (if (demand-matcher-demand-is-subscription? d) (not demand?) demand?)
	 (demand-matcher-pattern d)
	 (demand-matcher-meta-level d)
	 (+ 1 (max (demand-matcher-demand-level d)
		   (demand-matcher-supply-level d)))))

;; For each route "changed" in routes, if changed is one of our
;; monitored entities (a demand, if arrivals? is #t, or a supply
;; otherwise), including both a pattern, meta-level, and level match,
;; then search for matching peers (including level matching). If
;; arrivals? is #t, then if there are no matching peers (i.e. supplies
;; are not allocated), signel an increas in demand; otherwise, if
;; there are any matching peers (i.e. demand remains), signal a
;; decrease in supply.
(define (incorporate-delta arrivals? routes d state)
  (define relevant-change-detector (compute-detector arrivals? d))
  (define expected-change-level
    (if arrivals? (demand-matcher-demand-level d) (demand-matcher-supply-level d)))
  (define expected-peer-level
    (if arrivals? (demand-matcher-supply-level d) (demand-matcher-demand-level d)))
  (for/fold ([s state]) ([changed routes])
    (if (= (route-level changed) expected-change-level)
	(match (intersect-routes (list changed) (list relevant-change-detector))
	  ['() s]
	  [(list relevant-changed-route) ;; narrowed to relevancy by intersect-routes
	   ;; (log-info "incorporate-delta ~v ~v <--> ~v /// ~v"
	   ;; 	     arrivals?
	   ;; 	     relevant-changed-route
	   ;; 	     relevant-change-detector
	   ;; 	     (demand-matcher-state d))
	   (define peer-detector
	     (struct-copy route relevant-changed-route [level (+ 1 expected-peer-level)]))
	   (define peer-exists?
	     (ormap (lambda (r) (= (route-level r) expected-peer-level))
		    (intersect-routes (presence-detector-routes (demand-matcher-state d))
				      (list peer-detector))))
	   ;; (log-info "peer-exists? == ~v, peer-detector == ~v"
	   ;; 	     peer-exists?
	   ;; 	     peer-detector)
	   (cond
	    [(and arrivals? (not peer-exists?))
	     ((demand-matcher-increase-handler d) relevant-changed-route s)]
	    [(and (not arrivals?) peer-exists?)
	     ((demand-matcher-decrease-handler d) relevant-changed-route s)]
	    [else
	     s])])
	s)))

(define (demand-matcher-update d state0 rs)
  (define-values (new-state added removed) (presence-detector-update (demand-matcher-state d) rs))
  (define new-d (struct-copy demand-matcher d [state new-state]))
  (define state1 (incorporate-delta #t added new-d state0))
  (define state2 (incorporate-delta #f removed new-d state1))
  (values new-d state2))

(define (demand-matcher-handle-event e d)
  (match e
    [(routing-update routes)
     (define-values (new-d actions) (demand-matcher-update d '() routes))
     (transition new-d actions)]
    [_ #f]))

(define (spawn-demand-matcher pattern
			      increase-handler
			      [decrease-handler unexpected-supply-decrease]
			      #:demand-is-subscription? [demand-is-subscription? #t]
			      #:meta-level [meta-level 0]
			      #:demand-level [demand-level 0]
			      #:supply-level [supply-level 0])
  (define d (make-demand-matcher demand-is-subscription?
				 pattern
				 meta-level
				 demand-level
				 supply-level
				 (lambda (r actions) (cons (increase-handler r) actions))
				 (lambda (r actions) (cons (decrease-handler r) actions))))
  (spawn demand-matcher-handle-event
	 d
	 (list (compute-detector #t d)
	       (compute-detector #f d))))
