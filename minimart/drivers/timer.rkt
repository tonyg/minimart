#lang racket/base
;; Timer driver.

;; Uses mutable state internally, but because the scope of the
;; mutation is limited to each timer process alone, it's easy to show
;; correct linear use of the various pointers.

(require racket/set)
(require racket/match)
(require data/heap)
(require "../main.rkt")

(struct pending-timer (deadline label) #:transparent)

(provide (struct-out set-timer)
	 (struct-out timer-expired)
	 spawn-timer-driver)

(struct set-timer (label msecs kind) #:prefab)
(struct timer-expired (label msecs) #:prefab)

(struct driver-state (heap) #:transparent)

;; Racket's alarm-evt is almost the right design for timeouts: its
;; synchronisation value should be the (or some) value of the clock
;; after the asked-for time. That way it serves as timeout and
;; clock-reader in one.
(define (timer-evt msecs)
  (wrap-evt (alarm-evt msecs)
	    (lambda (_) (current-inexact-milliseconds))))

(define (make-timer-heap)
  (make-heap (lambda (t1 t2) (<= (pending-timer-deadline t1) (pending-timer-deadline t2)))))

(define (next-timer heap)
  (and (positive? (heap-count heap))
       (heap-min heap)))

(define (fire-timers! heap now)
  (if (zero? (heap-count heap))
      '()
      (let ((m (heap-min heap)))
	(if (<= (pending-timer-deadline m) now)
	    (begin (heap-remove-min! heap)
		   (cons (send (timer-expired (pending-timer-label m) now))
			 (fire-timers! heap now)))
	    '()))))

(define (timer-subscriptions s)
  (define t (next-timer (driver-state-heap s)))
  (gestalt-union (sub (set-timer ? ? 'relative))
		 (sub (set-timer ? ? 'absolute))
		 (pub (timer-expired ? ?))
		 (if t
		     (sub (event (timer-evt (pending-timer-deadline t)) ?) #:meta-level 1)
		     (gestalt-empty))))

(define (spawn-timer-driver)
  (define s (driver-state (make-timer-heap)))
  (spawn timer-driver
	 s
	 (timer-subscriptions s)))

(define (timer-driver e s)
  (match e
    [(message (event _ (list now)) 1 #f)
     (define actions (fire-timers! (driver-state-heap s) now))
     ;; Note: compute to-send before recursing, because of side-effects on heap
     (transition s (list (routing-update (timer-subscriptions s)) actions))]
    [(message (set-timer label msecs 'relative) 0 #f)
     (install-timer! s label (+ (current-inexact-milliseconds) msecs))]
    [(message (set-timer label msecs 'absolute) 0 #f)
     (install-timer! s label msecs)]
    [_ #f]))

(define (install-timer! s label deadline)
  (define now (current-inexact-milliseconds))
  (heap-add! (driver-state-heap s) (pending-timer deadline label))
  (transition s (routing-update (timer-subscriptions s))))
