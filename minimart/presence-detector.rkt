#lang racket/base

(require racket/set)
(require "core.rkt")
(require "pattern.rkt")

(provide (except-out (struct-out presence-detector) presence-detector)
	 (rename-out [make-presence-detector presence-detector])
	 presence-detector-update
	 presence-exists-for?)

(struct presence-detector (route-set) #:transparent)

(define (make-presence-detector [initial-routes '()])
  (presence-detector (list->set initial-routes)))

(define (presence-detector-update p rs)
  (define old-route-set (presence-detector-route-set p))
  (define new-route-set (list->set rs))
  (values (struct-copy presence-detector p [route-set new-route-set])
	  (set-subtract new-route-set old-route-set)
	  (set-subtract old-route-set new-route-set)))

(define (presence-exists-for? p probe-route)
  (for/or ((existing-route (in-set (presence-detector-route-set p))))
    (and (equal? (route-subscription? probe-route) (route-subscription? existing-route))
	 (equal? (route-meta-level probe-route) (route-meta-level existing-route))
	 (intersect? (route-pattern probe-route) (route-pattern existing-route)))))
