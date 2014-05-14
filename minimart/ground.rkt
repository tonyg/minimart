#lang racket/base

(require racket/set)
(require racket/match)
(require racket/list)
(require "core.rkt")

(provide (struct-out event)
	 run-ground)

(struct event (descriptor values) #:prefab)

(define (event-handler descriptor)
  (handle-evt descriptor (lambda vs (send (event descriptor vs)))))

(define event-projection (compile-gestalt-projection (event ?! ?)))

(define (extract-active-events gestalt)
  (define es (gestalt-project->finite-set gestalt 0 0 #f event-projection))
  ;; TODO: how should the following error be handled, ideally?
  ;; In principle, security restrictions should make it impossible.
  ;; But absent those, what should be done? Should an offending
  ;; process be identified and terminated?
  (when (not es) (error 'extract-active-events "User program subscribed to wildcard event"))
  (for/list [(ev (in-set es))]
    (match-define (vector e) ev)
    (event-handler e)))

(define idle-handler
  (handle-evt (system-idle-evt) (lambda _ #f)))

(define (run-ground . boot-actions)
  (let await-interrupt ((inert? #f) (p (spawn-world boot-actions)) (active-events '()))
    (define event-list (if inert?
			   active-events
			   (cons idle-handler active-events)))
    (if (null? event-list)
	(begin (log-info "run-ground: Terminating because inert")
	       (void))
	(let ((e (apply sync event-list)))
	  (match (deliver-event e -2 p)
	    [#f ;; inert
	     (await-interrupt #t p active-events)]
	    [(transition new-state actions)
	     (let process-actions ((actions (flatten actions)) (active-events active-events))
	       (match actions
		 ['()
		  (await-interrupt #f (struct-copy process p [state new-state]) active-events)]
		 [(cons a actions)
		  (match a
		    [(routing-update gestalt)
		     (process-actions actions (extract-active-events gestalt))]
		    [(quit)
		     (log-info "run-ground: Terminating by request")
		     (void)]
		    [_
		     (log-warning "run-ground: ignoring useless meta-action ~v" a)
		     (process-actions actions active-events)])]))])))))
