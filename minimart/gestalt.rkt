#lang racket/base
;; Gestalts: representations of (replicated) state.

(require racket/set)
(require racket/match)

(require "route.rkt")

(provide (struct-out gestalt)
	 gestalt-ref
	 compile-gestalt-projection
	 gestalt-project
	 gestalt-project->finite-set
	 drop-gestalt
	 lift-gestalt
	 simple-gestalt
	 gestalt-empty
	 gestalt-empty?
	 gestalt-combine
	 gestalt-combine-straight
	 gestalt-combine-crossed
	 gestalt-union
	 gestalt-intersect
	 gestalt-filter
	 gestalt-match
	 strip-gestalt-label
	 label-gestalt)

;; A Gestalt is a (gestalt (Listof (Listof (Pairof Matcher
;; Matcher)))), representing the total interests of a process or group
;; of processes. The outer list has a present entry for each active
;; metalevel, starting with metalevel 0 in the car. The inner lists
;; each have an entry for each active observer level at their
;; metalevel. The innermost pairs have cars holding matchers
;; representing active subscriptions, and cdrs representing active
;; advertisements.
;;
;;    "... a few standardised subsystems, identical from citizen to
;;     citizen. Two of these were channels for incoming data — one for
;;     gestalt, and one for linear, the two primary modalities of all
;;     Konishi citizens, distant descendants of vision and hearing."
;;      -- Greg Egan, "Diaspora"
;;         http://gregegan.customer.netspace.net.au/DIASPORA/01/Orphanogenesis.html
;;
(struct gestalt (metalevels) #:prefab)

;; Convention: A GestaltSet is a Gestalt where all the patterns map to
;; #t rather than a PID or any other value.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (safe-list-ref xs n [fail-thunk (lambda () (error 'safe-list-ref "No such index ~v" n))])
  (let loop ((xs xs) (n n))
    (match xs
      ['() (fail-thunk)]
      [(cons x xs) (if (zero? n) x (loop xs (- n 1)))])))

(define (safe-cdr xs)
  (if (null? xs)
      '()
      (cdr xs)))

(define (gestalt-ref g metalevel level get-advertisements?)
  (define v (safe-list-ref (gestalt-metalevels g) metalevel (lambda () '())))
  (define p (safe-list-ref v level (lambda () '(#f . #f))))
  ((if get-advertisements? cdr car) p))

(define (compile-gestalt-projection spec)
  (compile-projection spec))

(define (gestalt-project g metalevel level get-advertisements? capture-spec)
  (matcher-project (gestalt-ref g metalevel level get-advertisements?) capture-spec))

(define (gestalt-project->finite-set g metalevel level get-advertisements? capture-spec)
  (matcher->finite-set (gestalt-project g metalevel level get-advertisements? capture-spec)))

(define (drop-gestalt g)
  (match-define (gestalt metalevels) g)
  (if (null? metalevels) g (gestalt (cdr metalevels))))

(define (lift-gestalt g)
  (gestalt (cons '#() (gestalt-metalevels g))))

(define (prepend n x xs)
  (if (zero? n)
      xs
      (cons x (prepend (- n 1) x xs))))

(define (simple-gestalt subs advs level metalevel)
  (gestalt (prepend metalevel '() (list (prepend level '(#f . #f) (list (cons subs advs)))))))

(define (gestalt-empty) (gestalt '()))

(define (gestalt-empty? g)
  (andmap (lambda (ls) (andmap (lambda (l) (and (matcher-empty? (car l)) (matcher-empty? (cdr l)))) ls))
	  (gestalt-metalevels g)))

(define (map-zip imbalance-handler item-handler ls1 ls2)
  (let walk ((ls1 ls1) (ls2 ls2))
    (match* (ls1 ls2)
      [('() '()) '()]
      [('() ls) (imbalance-handler 'right-longer ls)]
      [(ls '()) (imbalance-handler 'left-longer ls)]
      [((cons l1 ls1) (cons l2 ls2))
       (define new-item (item-handler l1 l2))
       (define new-tail (walk ls1 ls2))
       (if (and (null? new-tail) (equal? new-item '(#f . #f)))
	   '()
	   (cons new-item new-tail))])))

(define (gestalt-combine g1 g2 imbalance-handler matcher-pair-combiner)
  (define (yu ls1 ls2) (map-zip imbalance-handler matcher-pair-combiner ls1 ls2))
  (define (xu mls1 mls2) (map-zip imbalance-handler yu mls1 mls2))
  (gestalt (xu (gestalt-metalevels g1)
	       (gestalt-metalevels g2))))

(define (gestalt-combine-straight g1 g2 imbalance-handler matcher-combiner)
  (gestalt-combine g1 g2
		   imbalance-handler
		   (lambda (sa1 sa2)
		     (cons (matcher-combiner (car sa1) (car sa2))
			   (matcher-combiner (cdr sa1) (cdr sa2))))))

(define (gestalt-combine-crossed g1 g2 imbalance-handler matcher-combiner)
  (gestalt-combine g1 g2
		   imbalance-handler
		   (lambda (sa1 sa2)
		     (cons (matcher-combiner (car sa1) (cdr sa2))
			   (matcher-combiner (car sa2) (cdr sa1))))))

(define (gestalt-union1 g1 g2) (gestalt-combine-straight g1 g2
							 (lambda (side x) x)
							 matcher-union))

(define (gestalt-union . gs)
  (if (null? gs)
      (gestalt-empty)
      (let walk ((gs gs))
	(match gs
	  [(list g) g]
	  [(cons g rest) (gestalt-union1 g (walk rest))]))))

(define (gestalt-intersect g1 g2) (gestalt-combine-straight g1 g2
							    (lambda (side x) '())
							    matcher-intersect))

;; View on g1 from g2's perspective.
;; Drops a level from g2 and intersects crossed.
(define (gestalt-filter g1 g2)
  (gestalt-combine-crossed g1
			   (gestalt (map safe-cdr (gestalt-metalevels g2)))
			   (lambda (side x) '())
			   (lambda (g1 g2) (matcher-intersect g1 g2
							      (lambda (v1 v2) v1)))))

(define (gestalt-match g1 g2)
  (define (zu sa1 sa2)
    (define-values (a1 a2) (matcher-match-matcher (car sa1) (car sa2)))
    (define-values (d1 d2) (matcher-match-matcher (cdr sa1) (cdr sa2)))
    (values (set-union a1 d1) (set-union a2 d2)))
  (define (mz xs1 xs2 f)
    (match* (xs1 xs2)
      [('() xs) (values (set) (set))]
      [(xs '()) (values (set) (set))]
      [((cons x1 xs1) (cons x2 xs2))
       (define-values (r1 r2) (mz xs1 xs2 f))
       (define-values (v1 v2) (f x1 x2))
       (values (set-union v1 r1) (set-union v2 r2))]))
  (define (yu ls1 ls2) (mz ls1 ls2 zu))
  (define (xu mls1 mls2) (mz mls1 mls2 yu))
  (xu (gestalt-metalevels g1)
      (gestalt-metalevels g2)))

(define (gestalt-matcher-transform g f)
  (define (zu sa) (cons (f (car sa)) (f (cdr sa))))
  (define (yu ls) (map zu ls))
  (define (xu mls) (map yu mls))
  (gestalt (xu (gestalt-metalevels g))))

(define (strip-gestalt-label g)
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (old) (set #t))))))

(define (label-gestalt g pid)
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (old) (set pid))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require rackunit)

  (check-equal? (simple-gestalt 'a 'b 0 0)
		(gestalt (list (list (cons 'a 'b)))))
  (check-equal? (simple-gestalt 'a 'b 2 2)
		(gestalt (list '() '() (list '(#f . #f)
					     '(#f . #f)
					     (cons 'a 'b))))))
