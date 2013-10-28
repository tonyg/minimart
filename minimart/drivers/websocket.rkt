#lang racket/base

(require racket/match)
(require net/rfc6455)
(require "../main.rkt")
(require "../demand-matcher.rkt")

(provide (struct-out websocket-remote-client)
	 (struct-out websocket-server)
	 (struct-out websocket-message)
	 spawn-websocket-driver)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol messages

(struct websocket-remote-client (id) #:prefab)
(struct websocket-server (port) #:prefab)
(struct websocket-message (from to body) #:prefab)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Driver

(define (spawn-websocket-driver)
  (spawn-demand-matcher (websocket-message ? (websocket-server ?) ?)
			#:demand-level 1
			#:supply-level 2
			(match-lambda
			 [(route _ (websocket-message _ (websocket-server port) _) _ _)
			  (spawn-websocket-listener port)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Listener

(struct listener-state (shutdown-procedure port) #:transparent)

(define (websocket-listener e state)
  (match e
    [(routing-update routes)
     (match-define (listener-state shutdown-procedure port) state)
     (define peer-listener-route (pub (websocket-message ? (websocket-server port) ?) #:level 2))
     (if (for/or ((r routes)) (pair? (intersect-routes (list r) (list peer-listener-route))))
	 #f
	 (begin (when shutdown-procedure (shutdown-procedure))
		(transition (struct-copy listener-state state [shutdown-procedure #f]) (quit))))]
    [(message (event _ (list (list c connection-shutdown-procedure))) 1 #f)
     (transition state
		 (spawn-connection (listener-state-port state)
				   c
				   connection-shutdown-procedure))]
    [_ #f]))

(define ((connection-handler listener-ch) c dummy-state)
  (define connection-ch (make-channel))
  (channel-put listener-ch (list c (lambda () (channel-put connection-ch #t))))
  (channel-get connection-ch)
  (ws-close! c))

(define (spawn-websocket-listener port)
  (define ch (make-channel))
  (define shutdown-procedure (ws-serve #:port port (connection-handler ch)))
  (spawn websocket-listener
	 (listener-state shutdown-procedure port)
	 (list (pub (websocket-message ? (websocket-server port) ?) #:level 2)
	       (sub (event ch ?) #:meta-level 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Connection

(struct connection-state (seen-peer? local-id port c shutdown-procedure) #:transparent)

(define (shutdown-connection state)
  (if (connection-state-shutdown-procedure state)
      (begin ((connection-state-shutdown-procedure state))
	     (transition (struct-copy connection-state state [shutdown-procedure #f]) (quit)))
      state))

(define (websocket-connection e state)
  (match e
    [(message (event _ _) 1 #f)
     (match-define (connection-state seen-peer? local-id port c _) state)
     (and seen-peer?
	  (let ((m (ws-recv c #:payload-type 'text)))
	    (if (eof-object? m)
		(shutdown-connection state)
		(transition state (send (websocket-message local-id
							   (websocket-server port)
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
    [#f #f]))

(define (spawn-connection port c shutdown-procedure)
  (define local-id (websocket-remote-client (gensym 'ws)))
  (spawn websocket-connection
	 (connection-state #f local-id port c shutdown-procedure)
	 (list (pub (websocket-message local-id (websocket-server port) ?))
	       (sub (websocket-message (websocket-server port) local-id ?))
	       (sub (websocket-message (websocket-server port) local-id ?) #:level 1)
	       (sub (event c ?) #:meta-level 1))))
