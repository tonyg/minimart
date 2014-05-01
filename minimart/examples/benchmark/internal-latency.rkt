#lang racket/base
;; Measurement of message delivery latency.

(require racket/match)
(require "../../main.rkt")

(struct ping (src dst timestamp) #:transparent)

(define (send-ping src dst)
  (send (ping src dst (current-inexact-milliseconds))))

(define (run #:echoer-count [echoer-count 100]
	     #:run-time [run-time 10000])
  (define total-latency 0)
  (define total-roundtrips 0)
  (define boot-start-time (current-inexact-milliseconds))
  (define run-start-time #f)

  (define (rate-at count)
    (/ (* count 2) ;; two messages per roundtrip
       (/ total-latency 1000.0) ;; latency in seconds
       ))

  (define (pinger src dst)
    (spawn (lambda (e s)
	     (match e
	       [(message 'kickoff _ _)
		(set! run-start-time (current-inexact-milliseconds))
		(transition s (send-ping src dst))]
	       [(message (ping (== dst) (== src) start-time) _ _)
		(define stop-time (current-inexact-milliseconds))
		(define delta (- stop-time start-time))
		(set! total-latency (+ total-latency delta))
		(set! total-roundtrips (+ total-roundtrips 1))
		(when (zero? (modulo total-roundtrips 1000))
		  (log-info "After ~a roundtrips, ~a milliseconds; ~a Hz"
			    total-roundtrips
			    total-latency
			    (rate-at total-roundtrips)))
		(transition s
			    (if (< (- stop-time run-start-time) run-time)
				(send-ping src dst)
				'()))]
	       [_ #f]))
	   #f
	   (list (sub (ping dst src ?))
		 (sub 'kickoff)
		 (pub (ping src dst ?)))))

  (define (echoer id)
    (spawn (lambda (e s)
	     (match e
	       [(message (ping src (== id) stamp) _ _)
		(transition s (send (ping id src stamp)))]
	       [_ #f]))
	   #f
	   (list (sub (ping ? id ?))
		 (pub (ping id ? ?)))))

  (begin
    (run-ground (for/list [(id (in-range echoer-count))] (echoer id))
		(pinger echoer-count 0)
		(send 'kickoff))
    (values total-roundtrips (rate-at total-roundtrips) (- run-start-time boot-start-time))))

(module+ main
  (define t 5000)
  (printf "Num echoers,Run duration (ms),Boot delay (ms),Num roundtrips,Msgs/sec,Sec/msg\n")
  (for ((n
	 (list 1 10 20 30 40 50 60 70 80 90 100 120
	       150 200 210 220 230 240 250 260 270 280 290 300 400
	       500 600 700 800 900)
	 ))
    (collect-garbage)
    (collect-garbage)
    (collect-garbage)
    (define-values (count v boot-delay-ms) (run #:echoer-count n #:run-time t))
    (printf "~a,~a,~a,~a,~a,~a\n" n t boot-delay-ms count v (/ 1.0 v))
    (flush-output)))
