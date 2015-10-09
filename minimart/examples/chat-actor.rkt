#lang minimart

(require (only-in racket/string string-trim))
(require "../drivers/tcp.rkt")
(require "../demand-matcher.rkt")

(define (spawn-session them us)
  (actor #:name user-session

	 (define (send-to-remote fmt . vs)
	   (send #:meta-level 1 (tcp-channel us them (string->bytes/utf-8 (apply format fmt vs)))))
	 (define (say who fmt . vs)
	   (unless (equal? who user) (send-to-remote "~a ~a\n" who (apply format fmt vs))))

	 (define user (gensym 'user))
	 (send-to-remote "Welcome, ~a.\n" user)

	 (advertise (tcp-channel us them ?) #:meta-level 1)
	 (subscribe `(,($ who) says ,($ what))
	   (say who "says: ~a" what))

	 (advertise `(,user says ,?))
	 (subscribe (tcp-channel them us ($ bs)) #:meta-level 1
	   (send `(,user says ,(string-trim (bytes->string/utf-8 bs)))))

 	 (observe-advertisers `(,($ who) says ,?)
	   #:name present-user-names
	   #:set who
	   #:added arrived
	   #:removed departed
	   (for/list [(who arrived)] (say who "arrived."))
	   (for/list [(who departed)] (say who "departed.")))

	 (observe-advertisers (tcp-channel them us ?) #:meta-level 1
	   #:presence remote-present?
	   (when (not remote-present?) (quit)))))

(spawn-tcp-driver)
(spawn-world
 (spawn-demand-matcher (tcp-channel (?! (tcp-address ? ?)) (?! (tcp-listener 5999)) ?)
		       #:meta-level 1
		       spawn-session))
