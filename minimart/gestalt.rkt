#lang racket/base
;; Gestalts: representations of (replicated) state.

(require racket/set)
(require racket/match)

(require "route.rkt")

(provide (struct-out gestalt)
	 gestalt-ref
	 compile-gestalt-projection
	 gestalt-project
	 matcher-project-level
	 levels->pids
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

;; A Gestalt is a (gestalt (Listof (Pairof Matcher Matcher))),
;; representing the total interests of a process or group of
;; processes. The outer list has a present entry for each active
;; metalevel, starting with metalevel 0 in the car. The inner pairs
;; have cars holding matchers representing active subscriptions, and
;; cdrs representing active advertisements. Each of the Matchers maps
;; to (Listof (Option (Setof PID))), with the nth entry in the list
;; corresponding to level n, and #f corresponding to empty-set.
;;
;; So,
;; - metalevels: entries in the outermost list.
;; - sub/adv: car or cdr of each inner pair, respectively.
;; - levels: entries in the list at each Matcher success value.
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

;; Convention: A GestaltSet is a Gestalt where all the Matchers map to
;; (Listof (Option #t)) rather than the (Listof (Option (Setof PID)))
;; described above or any other value.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (safe-list-ref xs n [fail-thunk (lambda () (error 'safe-list-ref "No such index ~v" n))])
  (let loop ((xs xs) (n n))
    (match xs
      ['() (fail-thunk)]
      [(cons x xs) (if (zero? n) x (loop xs (- n 1)))])))

(define (safe-take gcons xs n)
  (let walk ((xs xs) (n n))
    (cond [(null? xs) '()]
	  [(zero? n) '()]
	  [else (gcons (car xs) (walk (cdr xs) (- n 1)))])))

(define (safe-cdr xs)
  (if (null? xs)
      '()
      (cdr xs)))

(define ((guarded-cons unit) a d)
  (if (and (null? d) (equal? a unit))
      '()
      (cons a d)))

(define cons-level (guarded-cons #f))
(define cons-metalevel (guarded-cons '(#f . #f)))

;; Gestalt × Natural × Boolean → Matcher
(define (gestalt-ref g metalevel get-advertisements?)
  (define v (safe-list-ref (gestalt-metalevels g) metalevel (lambda () '(#f . #f))))
  ((if get-advertisements? cdr car) v))

(define (compile-gestalt-projection spec)
  (compile-projection spec))

;; Limits the given matcher to only include keys when a subscription
;; at *exactly* the given level exists.
(define (matcher-project-level m level)
  (matcher-relabel m (lambda (v) (and (safe-list-ref v level (lambda () #f)) #t))))

(define (gestalt-project g metalevel get-advertisements? capture-spec)
  (matcher-project (gestalt-ref g metalevel get-advertisements?) capture-spec))

(define (levels->pids ls)
  (foldl (lambda (e acc) (if e (set-union e acc) acc)) (set) ls))

(define (drop-gestalt g)
  (gestalt (safe-cdr (gestalt-metalevels g))))

(define (lift-gestalt g)
  (gestalt (cons-metalevel '(#f . #f) (gestalt-metalevels g))))

(define (prepend n x xs)
  (if (zero? n)
      xs
      (cons x (prepend (- n 1) x xs))))

(define (simple-gestalt is-adv? p level metalevel)
  (define m (pattern->matcher (prepend level #f (list #t)) p))
  (gestalt (prepend metalevel '(#f . #f) (list (if is-adv? (cons #f m) (cons m #f))))))

(define (gestalt-empty) (gestalt '()))

(define (gestalt-empty? g)
  (andmap (lambda (ml) (and (matcher-empty? (car ml)) (matcher-empty? (cdr ml))))
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
  (gestalt (map-zip imbalance-handler matcher-pair-combiner cons-metalevel
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

(define (empty->false s) (if (set-empty? s) #f s))

(define (union-levels m1 m2)
  (matcher-union m1 m2
		 #:combine
		 (lambda (ls1 ls2)
		   (map-zip (lambda (side x) x)
			    (lambda (s1 s2) (empty->false (set-union (or s1 (set)) (or s2 (set)))))
			    cons-level
			    ls1
			    ls2))))

(define (gestalt-union1 g1 g2) (gestalt-combine-straight g1 g2 (lambda (side x) x) union-levels))

(define (gestalt-union . gs)
  (if (null? gs)
      (gestalt-empty)
      (let walk ((gs gs))
	(match gs
	  [(list g) g]
	  [(cons g rest) (gestalt-union1 g (walk rest))]))))

(define (filter-levels ls1 ls2)
  (define r (safe-take cons-level ls1 (- (length ls2) 1)))
  (if (null? r) #f r))
(define (filter-matchers m1 m2) (matcher-intersect m1 m2 #:combine filter-levels))

;; View on g1 from g2's perspective.
;; Drops a level from g2 and intersects crossed.
(define (gestalt-filter g1 g2)
  (gestalt-combine-crossed g1 g2 (lambda (side x) '()) filter-matchers))

;; Here we want all pids in sets in ls2 such that there are some pids
;; at lower levels in ls1.
(define (match-combine-levels ls1 ls2 acc)
  (let loop ((ls1 ls1) (ls2 ls2))
    (cond
     [(null? ls1) acc]
     [(null? ls2) acc]
     [(not (car ls1)) (loop (cdr ls1) (cdr ls2))]
     [else ;; aha! here's a real sub/adv in ls1. The remaining
	   ;; sub/advs in (cdr ls2) can see it.
      (levels->pids (cdr ls2))])))

;; Much like gestalt-filter, takes a view on gestalt g1 from g2's
;; perspective. However, instead of returning the filtered g1, returns
;; just the set of values in the g2-map that were overlapped by some
;; part of g1.
(define (gestalt-match g1 g2)
  (let loop ((mls1 (gestalt-metalevels g1))
	     (mls2 (gestalt-metalevels g2)))
    (cond [(null? mls1) (set)]
	  [(null? mls2) (set)]
	  [else (match-define (cons subs1 advs1) (car mls1))
		(match-define (cons subs2 advs2) (car mls2))
		(let* ((acc (loop (cdr mls1) (cdr mls2)))
		       (acc (matcher-match-matcher subs1 advs2
						   #:combine match-combine-levels
						   #:empty acc))
		       (acc (matcher-match-matcher advs1 subs2
						   #:combine match-combine-levels
						   #:empty acc)))
		  acc)])))

(define (erase-imbalance-handler side x)
  (case side
    [(left-longer) x]
    [(right-longer) '()]))

(define (erase-levels ls1 ls2)
  (map-zip erase-imbalance-handler
	   (lambda (v1 v2) (empty->false (set-subtract (or v1 (set)) (or v2 (set)))))
	   cons-level
	   ls1
	   ls2))

(define (gestalt-erase-path g1 g2)
  (gestalt-combine-straight g1 g2
			    erase-imbalance-handler
			    (lambda (m1 m2) (matcher-erase-path m1 m2 #:combine erase-levels))))

(define ((guarded-map gcons) f xs)
  (foldr (lambda (e acc) (gcons (f e) acc)) '() xs))

(define map-metalevels (guarded-map cons-metalevel))

(define (gestalt-matcher-transform g f)
  (gestalt (map-metalevels (lambda (p) (cons (f (car p)) (f (cdr p))))
			   (gestalt-metalevels g))))

(define (strip-gestalt-label g)
  (define (xform ls) (map (lambda (l) (and l #t)) ls))
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m xform))))

(define (label-gestalt g pid)
  (define pidset (set pid))
  (define (xform ls) (map (lambda (l) (and l pidset)) ls))
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m xform))))

(define (pretty-print-gestalt g [port (current-output-port)])
  (for [(metalevel (in-naturals)) (p (in-list (gestalt-metalevels g)))]
    (match-define (cons subs advs) p)
    (when (or subs advs)
      (fprintf port "GESTALT metalevel ~v:\n" metalevel)
      (when subs (fprintf port "  - subs:") (pretty-print-matcher subs port #:indent 9))
      (when advs (fprintf port "  - advs:") (pretty-print-matcher advs port #:indent 9)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require rackunit)

  (check-equal? (gestalt-union (simple-gestalt #f 'a 0 0)
			       (simple-gestalt #t 'b 0 0))
		(gestalt (list (cons (pattern->matcher (list #t) 'a)
				     (pattern->matcher (list #t) 'b)))))
  (check-equal? (gestalt-union (simple-gestalt #f 'a 2 2)
			       (simple-gestalt #t 'b 2 2))
		(gestalt (list (cons #f #f)
			       (cons #f #f)
			       (cons (pattern->matcher (list #f #f #t) 'a)
				     (pattern->matcher (list #f #f #t) 'b))))))
