#lang racket/base

(require "core.rkt")
(require "presence-detector.rkt")

(provide (except-out (struct-out demand-matcher) demand-matcher)
	 (rename-out [make-demand-matcher demand-matcher])
	 demand-matcher-update)

(struct demand-matcher (subscription-is-demand? increase-handler decrease-handler state)
	#:transparent)

(define (default-decrease-handler removed state)
  (error 'demand-matcher "Unexpected decrease in supply for route ~a" removed))

(define (make-demand-matcher increase-handler
			     [decrease-handler default-decrease-handler]
			     #:subscription-is-demand? [subscription-is-demand? #t])
  (demand-matcher subscription-is-demand?
		  increase-handler
		  decrease-handler
		  (presence-detector)))

(define (demand-matcher-update d state0 rs)
  (define-values (new-state added removed) (presence-detector-update (demand-matcher-state d)))
  (define state1 (for/fold ([s state0]) ([r added]) ((demand-matcher-increase-handler d) r s)))
  (define state2 (for/fold ([s state1]) ([r removed]) ((demand-matcher-decrease-handler d) r s)))
  (values (struct-copy demand-matcher d [state new-state])
	  state2))
