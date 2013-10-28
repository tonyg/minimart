#lang racket/base

(require racket/match)
(require racket/list)
(require "core.rkt")

(provide (struct-out event)
	 run-ground)

(struct event (descriptor values) #:prefab)

(define (event-handler descriptor)
  (handle-evt descriptor (lambda vs (send (event descriptor vs)))))

(define (extract-active-events routes)
  (filter-map (lambda (r)
		(and (route-subscription? r)
		     (zero? (route-meta-level r))
		     (zero? (route-level r))
		     (match (route-pattern r)
		       [(event descriptor (? wildcard?)) (event-handler descriptor)]
		       [_ #f])))
	      routes))

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
	  (log-info "Woke: ~v" e)
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
		    [(routing-update routes)
		     (process-actions actions (extract-active-events routes))]
		    [(quit)
		     (log-info "run-ground: Terminating by request")
		     (void)]
		    [_
		     (log-warning "run-ground: ignoring useless meta-action ~v" a)
		     (process-actions actions active-events)])]))])))))
