#lang minimart

(require (only-in racket/port read-line-evt))
(require "../drivers/timer.rkt")

(define (quasi-spy e s)
  (printf "----------------------------------------\n")
  (printf "QUASI-SPY:\n")
  (match e
    [(routing-update g) (pretty-print-gestalt g)]
    [other
     (write other)
     (newline)])
  (printf "========================================\n")
  #f)
(spawn quasi-spy (void) (gestalt-union (sub ? #:level 10 #:meta-level 1)
				       (pub ? #:level 10 #:meta-level 1)
				       (sub ? #:level 10)
				       (pub ? #:level 10)))

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

(spawn-world (spawn r (void) (sub ?))
	     (spawn b 0))

(define (echoer e s)
  (match e
    [(message (event _ (list (? eof-object?))) _ _) (transition s (quit))]
    [(message (event _ (list line)) _ _) (transition s (send `(print got-line ,line)))]
    [_ #f]))

(spawn echoer (void) (sub (event (read-line-evt (current-input-port) 'any) ?)
			  #:meta-level 1))

(define (ticker e s)
  (match e
    [(routing-update g)
     (printf "EMPTY? ~v\n" (gestalt-empty? g))
     (printf "INTERSECTED:\n")
     (pretty-print-gestalt (gestalt-filter g (pub (set-timer ? ? ?) #:level 1)))
     #f]
    [(message (timer-expired 'tick now) _ _)
     (printf "TICK ~v\n" now)
     (transition (+ s 1) (if (< s 3)
			     (send (set-timer 'tick 1000 'relative))
			     (quit)))]
    [_ #f]))

(spawn-timer-driver)
(send (set-timer 'tick 1000 'relative))
(spawn ticker 1 (gestalt-union (pub (set-timer ? ? ?) #:level 1)
			       (sub (timer-expired 'tick ?))))

(define (printer e s)
  (match e
    [(message (cons 'print v) _ _)
     (log-info "PRINTER: ~a" v)
     #f]
    [_ #f]))

(spawn printer (void) (sub `(print . ,?)))
