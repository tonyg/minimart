#lang racket/base

(require racket/set)
(require racket/match)
(require "core.rkt")

(provide (except-out (struct-out presence-detector) presence-detector)
	 (rename-out [make-presence-detector presence-detector])
	 presence-detector-update
	 presence-detector-routes)

(struct presence-detector (route-set) #:transparent)

(define (make-presence-detector [initial-routes '()])
  (presence-detector (list->set initial-routes)))

(define (presence-detector-update p rs)
  (define old-route-set (presence-detector-route-set p))
  (define new-route-set (list->set rs))
  (values (struct-copy presence-detector p [route-set new-route-set])
	  (set-subtract new-route-set old-route-set)
	  (set-subtract old-route-set new-route-set)))

(define (presence-detector-routes p)
  (set->list (presence-detector-route-set p)))
