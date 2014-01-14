#lang minimart

(require "../drivers/websocket.rkt")
(require "../demand-matcher.rkt")

(spawn-websocket-driver)

(define any-client (websocket-remote-client ?))
(define server-id (websocket-local-server 8081 #f))

(spawn-demand-matcher (websocket-message any-client server-id ?)
		      #:demand-is-subscription? #f
		      (match-lambda ;; arrived-demand-route, i.e. new connection publisher
		       [(route _ (websocket-message c _ _) _ _)
			(spawn-connection-handler c)]
		       [_ '()])
		      (lambda (departed-supply-route)
			(log-info "Connection handler decided to exit")
			'()))

(define (spawn-connection-handler c)
  (log-info "spawn-connection-handler ~v" c)
  (define (connection-handler e n)
    (when e (log-info "connection-handler ~v: ~v /// ~v" c e n))
    (match e
      [(routing-update '()) (transition n (quit))]
      [_
       (if (< n 20)
	   (transition (+ n 1) (send (websocket-message server-id c (format "msg ~v" n))))
	   #f)]))
  (spawn connection-handler
	 0
	 (list (sub (websocket-message c server-id ?))
	       (sub (websocket-message c server-id ?) #:level 1)
	       (pub (websocket-message server-id c ?)))))
