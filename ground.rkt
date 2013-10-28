#lang racket/base

(require racket/match)
(require racket/list)
(require "core.rkt")
(require "pattern.rkt")

(provide (struct-out event)
	 run-actor)

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

(define (run-actor p)
  (let await-interrupt ((inert? #f) (p p) (active-events '()))
    (define event-list (if inert?
			   active-events
			   (cons idle-handler active-events)))
    (define e (apply sync event-list))
    (log-info "Woke: ~v" e)
    (match (deliver-event e -1 p)
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
	       (log-info "run-actor: Exiting by request")
	       (void)]
	      [_
	       (log-warning "run-actor: ignoring useless meta-action ~v" a)
	       (process-actions actions active-events)])]))])))
