#lang racket/base
;; Gestalts: representations of (replicated) state.

(require racket/set)
(require racket/match)

(require "route.rkt")

(provide (struct-out gestalt)
	 gestalt-match-value
	 compile-gestalt-projection
	 gestalt-project
	 drop-gestalt
	 lift-gestalt
	 simple-gestalt
	 gestalt-empty
	 gestalt-empty?
	 gestalt-union
	 gestalt-filter
	 gestalt-match
	 gestalt-erase-path
	 strip-gestalt-label
	 label-gestalt
	 pretty-print-gestalt)

;; A Gestalt is a (gestalt (Listof (Listof (Pairof Matcher Matcher)))),
;; representing the total interests of a process or group of
;; processes.
;;
;; The outer list has an entry for each active metalevel, starting
;; with metalevel 0 in the car.
;;
;; The middle list has an entry for each active level within its
;; metalevel, starting with level 0 in the car.
;;
;; The inner pairs have cars holding matchers representing active
;; subscriptions, and cdrs representing active advertisements.
;;
;; Each of the Matchers maps to (NonemptySetof PID).
;;
;;
;;    "... a few standardised subsystems, identical from citizen to
;;     citizen. Two of these were channels for incoming data — one for
;;     gestalt, and one for linear, the two primary modalities of all
;;     Konishi citizens, distant descendants of vision and hearing."
;;      -- Greg Egan, "Diaspora"
;;         http://gregegan.customer.netspace.net.au/DIASPORA/01/Orphanogenesis.html
;;
(struct gestalt (metalevels) #:prefab)

;; Convention: A GestaltSet is a Gestalt where the Matchers map to #t
;; instead of (NonemptySetof PID) or any other value.

;; TODO: consider caching the unioning that happens when a high-level
;; subscription is smeared across lower levels for the purposes of
;; filtering and matching of routing-updates.

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

(define ((guarded-cons unit) a d)
  (if (and (null? d) (equal? a unit))
      '()
      (cons a d)))

(define (guarded-map gcons f xs)
  (foldr (lambda (e acc) (gcons (f e) acc)) '() xs))

(define empty-level '(#f . #f))
(define empty-metalevel '())

(define cons-level (guarded-cons empty-level))
(define cons-metalevel (guarded-cons empty-metalevel))

;; Gestalt × Value × Natural × Boolean → (Setof PID)
(define (gestalt-match-value g body metalevel is-feedback?)
  (define levels (safe-list-ref (gestalt-metalevels g) metalevel (lambda () empty-metalevel)))
  (for/fold [(acc (set))] [(level (in-list levels))]
    (define matcher ((if is-feedback? cdr car) level)) ;; feedback targets advertisers/publishers
    (set-union (matcher-match-value matcher body) acc)))

(define (compile-gestalt-projection spec)
  (compile-projection spec))

;; Gestalt × Natural × Natural × Boolean × CompiledSpec → Matcher
(define (gestalt-project g metalevel level get-advertisements? capture-spec)
  (define levels (safe-list-ref (gestalt-metalevels g) metalevel (lambda () empty-metalevel)))
  (define matcher ((if get-advertisements? cdr car)
		   (safe-list-ref levels level (lambda () empty-level))))
  (matcher-project matcher capture-spec))

(define (drop-gestalt g)
  (gestalt (safe-cdr (gestalt-metalevels g))))

(define (lift-gestalt g)
  (gestalt (cons-metalevel empty-metalevel (gestalt-metalevels g))))

(define (prepend n x xs)
  (if (zero? n)
      xs
      (cons x (prepend (- n 1) x xs))))

(define (simple-gestalt is-adv? p level metalevel)
  (define m (pattern->matcher #t p))
  (gestalt (prepend metalevel empty-metalevel
		    (list (prepend level empty-level
				   (list (if is-adv? (cons #f m) (cons m #f))))))))

(define (gestalt-empty) (gestalt '()))

(define (gestalt-empty? g)
  (andmap (lambda (ml)
	    (andmap (lambda (l) (and (matcher-empty? (car l)) (matcher-empty? (cdr l)))) ml))
	  (gestalt-metalevels g)))

(define (map-zip imbalance-handler item-handler gcons ls1 ls2)
  (let walk ((ls1 ls1) (ls2 ls2))
    (match* (ls1 ls2)
      [('() '()) '()]
      [('() ls) (imbalance-handler 'right-longer ls)]
      [(ls '()) (imbalance-handler 'left-longer ls)]
      [((cons l1 ls1) (cons l2 ls2))
       (gcons (item-handler l1 l2) (walk ls1 ls2))])))

(define (gestalt-combine g1 g2 imbalance-handler matcher-pair-combiner)
  (gestalt (map-zip imbalance-handler
		    (lambda (ls1 ls2)
		      (map-zip imbalance-handler matcher-pair-combiner cons-level ls1 ls2))
		    cons-metalevel
		    (gestalt-metalevels g1)
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

(define (gestalt-union . gs)
  (if (null? gs)
      (gestalt-empty)
      (let walk ((gs gs))
	(match gs
	  [(list g) g]
	  [(cons g rest) (gestalt-union1 g (walk rest))]))))

(define (gestalt-union1 g1 g2) (gestalt-combine-straight g1 g2 (lambda (side x) x) matcher-union))

(define (shorter-imbalance-handler side x) '())

;; View on g1 from g2's perspective.
(define (gestalt-filter g1 g2)
  (gestalt (map-zip shorter-imbalance-handler
		    filter-one-metalevel
		    cons-metalevel
		    (gestalt-metalevels g1)
		    (gestalt-metalevels g2))))

;; Much like gestalt-filter, takes a view on gestalt g1 from g2's
;; perspective. However, instead of returning the filtered g1, returns
;; just the set of values in the g2-map that were overlapped by some
;; part of g1.
(define (gestalt-match g1 g2)
  (let loop ((mls1 (gestalt-metalevels g1))
	     (mls2 (gestalt-metalevels g2)))
    (cond [(null? mls1) (set)]
	  [(null? mls2) (set)]
	  [else (match-define (cons ls1 rest1) mls1)
		(match-define (cons ls2 rest2) mls2)
		(set-union (match-one-metalevel ls1 ls2)
			   (loop rest1 rest2))])))

;; Returns ls, with one level dropped, and with the remaining matchers
;; "smeared" across lower levels. This could end up being reasonably
;; expensive - see above TODO about possibly caching it.
(define (smear-levels ls)
  (foldr (lambda (p acc)
	   (match-define (cons acc-subs acc-advs) (if (null? acc) empty-level (car acc)))
	   (match-define (cons new-subs new-advs) p)
	   (cons (cons (matcher-union new-subs acc-subs)
		       (matcher-union new-advs acc-advs))
		 acc))
	 '()
	 (safe-cdr ls)))

(define (filter-one-metalevel ls1 ls2)
  (let loop ((ls1 ls1) (ls2 (smear-levels ls2)))
    (cond [(null? ls1) '()]
	  [(null? ls2) '()]
	  [else (match-define (cons (cons subs1 advs1) rest1) ls1)
		(match-define (cons (cons subs2 advs2) rest2) ls2)
		(cons-level (cons (matcher-intersect subs1 advs2 #:combine (lambda (v1 v2) v1))
				  (matcher-intersect advs1 subs2 #:combine (lambda (v1 v2) v1)))
			    (loop rest1 rest2))])))

(define (match-matchers m1 m2)
  (matcher-match-matcher m1 m2 #:combine (lambda (v1 v2 acc) (set-union v2 acc)) #:empty (set)))

(define (match-one-metalevel ls1 ls2)
  (let loop ((ls1 ls1) (ls2 (smear-levels ls2)))
    (cond [(null? ls1) (set)]
	  [(null? ls2) (set)]
	  [else (match-define (cons (cons subs1 advs1) rest1) ls1)
		(match-define (cons (cons subs2 advs2) rest2) ls2)
		(set-union (match-matchers subs1 advs2)
			   (match-matchers advs1 subs2)
			   (loop rest1 rest2))])))

(define (gestalt-erase-path g1 g2)
  (gestalt-combine-straight g1 g2
			    erase-imbalance-handler
			    matcher-erase-path))

(define (erase-imbalance-handler side x)
  (case side
    [(left-longer) x]
    [(right-longer) '()]))

(define (gestalt-matcher-transform g f)
  (gestalt (guarded-map cons-metalevel
			(lambda (ls)
			  (guarded-map cons-level (lambda (p) (cons (f (car p)) (f (cdr p)))) ls))
			(gestalt-metalevels g))))

(define (strip-gestalt-label g)
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (v) #t)))))

(define (label-gestalt g pid)
  (define pidset (set pid))
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (v) pidset)))))

(define (pretty-print-gestalt g [port (current-output-port)])
  (for [(metalevel (in-naturals)) (ls (in-list (gestalt-metalevels g)))]
    (for [(level (in-naturals)) (p (in-list ls))]
      (match-define (cons subs advs) p)
      (when (or subs advs)
	(fprintf port "GESTALT metalevel ~v level ~v:\n" metalevel level)
	(when subs (fprintf port "  - subs:") (pretty-print-matcher subs port #:indent 9))
	(when advs (fprintf port "  - advs:") (pretty-print-matcher advs port #:indent 9))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require rackunit)

  (check-equal? (simple-gestalt #f 'a 0 0)
		(gestalt (list (list (cons (pattern->matcher #t 'a) #f)))))
  (check-equal? (simple-gestalt #t 'b 0 0)
		(gestalt (list (list (cons #f (pattern->matcher #t 'b))))))
  (check-equal? (simple-gestalt #f 'a 2 2)
		(gestalt (list empty-metalevel empty-metalevel
			       (list empty-level empty-level
				     (cons (pattern->matcher #t 'a) #f)))))
  (check-equal? (simple-gestalt #t 'b 2 2)
		(gestalt (list empty-metalevel empty-metalevel
			       (list empty-level empty-level
				     (cons #f (pattern->matcher #t 'b))))))

  (check-equal? (gestalt-union (simple-gestalt #f 'a 0 0)
			       (simple-gestalt #t 'b 0 0))
		(gestalt (list (list (cons (pattern->matcher #t 'a)
					   (pattern->matcher #t 'b))))))
  (check-equal? (gestalt-union (simple-gestalt #f 'a 2 2)
			       (simple-gestalt #t 'b 2 2))
		(gestalt (list empty-metalevel empty-metalevel
			       (list empty-level empty-level
				     (cons (pattern->matcher #t 'a)
					   (pattern->matcher #t 'b)))))))
