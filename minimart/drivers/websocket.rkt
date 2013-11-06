#lang racket/base

(require racket/match)
(require net/rfc6455)
(require "../main.rkt")
(require "../demand-matcher.rkt")

(require racket/unit)
(require net/tcp-sig)
(require net/tcp-unit)
(require net/ssl-tcp-unit)

(provide (struct-out websocket-remote-client)
	 (struct-out websocket-server)
	 (struct-out websocket-ssl-options)
	 (struct-out websocket-message)
	 spawn-websocket-driver)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol messages

(struct websocket-remote-client (id) #:prefab)
(struct websocket-server (port ssl-options) #:prefab)
(struct websocket-ssl-options (cert-file key-file) #:prefab)
(struct websocket-message (from to body) #:prefab)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Driver

(define (spawn-websocket-driver)
  (spawn-demand-matcher (websocket-message ? (websocket-server ? ?) ?)
			#:demand-level 1
			#:supply-level 2
			(match-lambda
			 [(route _ (websocket-message _ server-addr _) _ _)
			  (spawn-websocket-listener server-addr)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Listener

(struct listener-state (shutdown-procedure server-addr) #:transparent)

(define (websocket-listener e state)
  (match e
    [(routing-update routes)
     (match-define (listener-state shutdown-procedure server-addr) state)
     (define peer-listener-route (pub (websocket-message ? server-addr ?) #:level 2))
     (if (for/or ((r routes)) (pair? (intersect-routes (list r) (list peer-listener-route))))
	 #f
	 (begin (when shutdown-procedure (shutdown-procedure))
		(transition (struct-copy listener-state state [shutdown-procedure #f]) (quit))))]
    [(message (event _ (list (list c connection-shutdown-procedure))) 1 #f)
     (transition state
		 (spawn-connection (listener-state-server-addr state)
				   c
				   connection-shutdown-procedure))]
    [_ #f]))

(define ((connection-handler listener-ch) c dummy-state)
  (define connection-ch (make-channel))
  (channel-put listener-ch (list c (lambda () (channel-put connection-ch #t))))
  (channel-get connection-ch)
  (ws-close! c))

(define (ssl-options->ssl-tcp@ ssl-options)
  (match-define (websocket-ssl-options cert-file key-file) ssl-options)
  (define-unit-binding ssl-tcp@
    (make-ssl-tcp@ cert-file key-file #f #f #f #f #f)
    (import)
    (export tcp^))
  ssl-tcp@)

(define (spawn-websocket-listener server-addr)
  (match-define (websocket-server port ssl-options) server-addr)
  (define ch (make-channel))
  (define shutdown-procedure (ws-serve #:port port
				       #:tcp@ (if ssl-options
						  (ssl-options->ssl-tcp@ ssl-options)
						  tcp@)
				       (connection-handler ch)))
  (spawn websocket-listener
	 (listener-state shutdown-procedure server-addr)
	 (list (pub (websocket-message ? server-addr ?) #:level 2)
	       (sub (event ch ?) #:meta-level 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Connection

(struct connection-state (seen-peer? local-addr server-addr c [shutdown-procedure #:mutable])
	#:transparent)

(define (shutdown-connection state)
  (when (connection-state-shutdown-procedure state)
    ((connection-state-shutdown-procedure state))
    (set-connection-state-shutdown-procedure! state #f))
  (transition state (quit)))

(define (websocket-connection e state)
  (with-handlers [((lambda (exn) #t)
		   (lambda (exn) (shutdown-connection state)))]
    (match e
      [(message (event _ _) 1 #f)
       (match-define (connection-state seen-peer? local-addr server-addr c _) state)
       (and seen-peer?
	    (let ((m (ws-recv c #:payload-type 'text)))
	      (if (eof-object? m)
		  (shutdown-connection state)
		  (transition state (send (websocket-message local-addr
							     server-addr
							     m))))))]
      [(message (websocket-message _ _ m) 0 #f)
       (ws-send! (connection-state-c state) m)
       #f]
      [(routing-update routes)
       (cond
	[(and (connection-state-seen-peer? state) (null? routes))
	 (shutdown-connection state)]
	[(and (not (connection-state-seen-peer? state)) (pair? routes))
	 (transition (struct-copy connection-state state [seen-peer? #t]) '())]
	[else
	 #f])]
      [#f #f])))

(define (spawn-connection server-addr c shutdown-procedure)
  (define local-addr (websocket-remote-client (gensym 'ws)))
  (spawn websocket-connection
	 (connection-state #f local-addr server-addr c shutdown-procedure)
	 (list (pub (websocket-message local-addr server-addr ?))
	       (sub (websocket-message server-addr local-addr ?))
	       (sub (websocket-message server-addr local-addr ?) #:level 1)
	       (sub (event c ?) #:meta-level 1))))
