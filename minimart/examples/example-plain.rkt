#lang racket/base

(require racket/match)
(require (only-in racket/port read-line-evt))
(require "../main.rkt")
(require "../drivers/timer.rkt")

(define (r e s)
  (match e
    [(message body _ _) (transition s (send `(print got ,body) #:meta-level 1))]
    [_ #f]))

(define (b e n)
  (match e
    [#f (if (< n 10)
	    (transition (+ n 1) (send `(hello ,n)))
	    #f)]
    [_ #f]))

(define (echoer e s)
  (match e
    [(message (event _ (list (? eof-object?))) _ _) (transition s (quit))]
    [(message (event _ (list line)) _ _) (transition s (send `(print got-line ,line)))]
    [_ #f]))

(define (ticker e s)
  (match e
    [(routing-update g)
     (printf "EMPTY? ~v\n" (gestalt-empty? g))
     (printf "REF:")
     (pretty-print-matcher (gestalt-ref g 0 0 #f) #:indent 4)
     (printf "INTERSECTED:\n")
     (pretty-print-gestalt (gestalt-intersect g (sub (set-timer ? ? ?))))
     #f]
    [(message (timer-expired 'tick now) _ _)
     (printf "TICK ~v\n" now)
     (transition (+ s 1) (if (< s 3)
			     (send (set-timer 'tick 1000 'relative))
			     (quit)))]
    [_ #f]))

(define (printer e s)
  (match e
    [(message (cons 'print v) _ _)
     (log-info "PRINTER: ~a" v)
     #f]
    [_ #f]))

(run-ground (spawn-timer-driver)
	    (send (set-timer 'tick 1000 'relative))
	    (spawn ticker 1 (gestalt-union (pub (set-timer ? ? ?) #:level 1)
					   (sub (timer-expired 'tick ?))))
	    (spawn-world (spawn r (void) (sub ?))
			 (spawn b 0))
	    (spawn echoer (void) (sub (event (read-line-evt (current-input-port) 'any) ?)
				      #:meta-level 1))
	    (spawn printer (void) (sub `(print . ,?))))
