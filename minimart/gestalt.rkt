#lang racket/base
;; Gestalts: representations of (replicated) state.

(require racket/set)
(require racket/match)
(require (only-in racket/list make-list))
(require (only-in racket/port with-output-to-string))

(require "route.rkt")
(require "tset.rkt")

(provide (struct-out gestalt)
	 (struct-out projection)
	 gestalt-match-value

	 project-subs
	 project-pubs
	 projection?
	 projection-spec
	 projection->gestalt
	 gestalt-project*
	 gestalt-project
	 gestalt-project/keys
	 gestalt-project/single

	 drop-gestalt
	 lift-gestalt
	 simple-gestalt
	 gestalt-empty
	 gestalt-empty?
	 gestalt-full
	 gestalt-union*
	 gestalt-union
	 gestalt-filter
	 gestalt-match
	 gestalt-subtract
	 gestalt-transform
	 gestalt-matcher-transform
	 strip-gestalt-label
	 label-gestalt
	 gestalt-level-count
	 pretty-print-gestalt
	 gestalt->pretty-string
	 gestalt->jsexpr
	 jsexpr->gestalt)

;; A Gestalt is a (gestalt (Listof Metalevel)), representing the total
;; interests of a process or group of processes at all metalevels and
;; levels.
;;
;; A Level is a (Pairof Matcher Matcher), representing active
;; subscriptions and advertisements at a particular level and
;; metalevel.
;;
;; A Metalevel is a (Listof Level), representing all Levels (ordered
;; by level number) at a given metalevel.
;;
;; --
;;
;; The outer list of a Gestalt has an entry for each active metalevel,
;; starting with metalevel 0 in the car.
;;
;; The middle list has an entry for each active level within its
;; metalevel, starting with level 0 in the car.
;;
;; The inner pairs have cars holding matchers representing active
;; subscriptions, and cdrs representing active advertisements.
;;
;; Each of the Matchers maps to (NonemptySetof PID).
;;
;; --
;;
;;    "... a few standardised subsystems, identical from citizen to
;;     citizen. Two of these were channels for incoming data — one for
;;     gestalt, and one for linear, the two primary modalities of all
;;     Konishi citizens, distant descendants of vision and hearing."
;;      -- Greg Egan, "Diaspora"
;;         http://gregegan.customer.netspace.net.au/DIASPORA/01/Orphanogenesis.html
;;
(struct gestalt (metalevels)
	#:transparent
	#:methods gen:custom-write
	[(define (write-proc g port mode)
	   (display "{{{" port)
	   (pretty-print-gestalt g port)
	   (display "}}}" port))])

;; Convention: A GestaltSet is a Gestalt where the Matchers map to #t
;; instead of (NonemptySetof PID) or any other value.

;; A GestaltProjection is a single-metalevel, single-level fragment of
;; a gestalt with capture-groups. See matcher-project in route.rkt.
(struct projection (metalevel level get-advertisements? spec compiled))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (Listof X) Nat [-> X] -> X
(define (safe-list-ref xs n [fail-thunk (lambda () (error 'safe-list-ref "No such index ~v" n))])
  (let loop ((xs xs) (n n))
    (match xs
      ['() (fail-thunk)]
      [(cons x xs) (if (zero? n) x (loop xs (- n 1)))])))

;; (Listof X) -> (Listof X)
;; ->> HISTORICAL IRONY <<-
(define (safe-cdr xs)
  (if (null? xs)
      '()
      (cdr xs)))

;; X -> X (Listof X) -> (Listof X)
;; Conses a onto d, unless d is '() and a is the special unit value.
(define ((guarded-cons unit) a d)
  (if (and (null? d) (equal? a unit))
      '()
      (cons a d)))

;; Level
;; The empty level, matching no messages.
(define empty-level '(#f . #f))

;; The empty metalevel, matching no messages at any level.
(define empty-metalevel '())

;; Level Metalevel -> Metalevel
;; Only adds to its second argument if its first is nonempty.
(define cons-level (guarded-cons empty-level))

;; Metalevel (Listof Metalevel) -> (Listof Metalevel).
;; Only adds to its second argument if its first is nonempty.
(define cons-metalevel (guarded-cons empty-metalevel))

;; Gestalt Nat -> Metalevel
(define (gestalt-metalevel-ref g n)
  (safe-list-ref (gestalt-metalevels g) n (lambda () empty-metalevel)))

;; Gestalt × Value × Natural × Boolean → (Setof PID)
;; Retrieves those PIDs that have active subscriptions/advertisements
;; covering the given message at the given metalevel.
(define (gestalt-match-value g body metalevel is-feedback?)
  (define extract-matcher (if is-feedback? cdr car)) ;; feedback targets advertisers/publishers
  (define (pids-at level) (matcher-match-value (extract-matcher level) body))
  (foldr tset-union (datum-tset) (map pids-at (gestalt-metalevel-ref g metalevel))))

;; project-subs : Projection [#:meta-level Nat] [#:level Nat] -> GestaltProjection
;; project-pubs : Projection [#:meta-level Nat] [#:level Nat] -> GestaltProjection
;;
;; Construct projectors representing subscriptions/advertisements
;; matching the given pattern, at the given meta-level and level.
;; Used with gestalt-project.
(define (project-subs p #:meta-level [ml 0] #:level [l 0])
  (projection ml l #f p (compile-projection p)))
(define (project-pubs p #:meta-level [ml 0] #:level [l 0])
  (projection ml l #t p (compile-projection p)))

;; GestaltProjection -> Gestalt
;; Converts a projection to an atomic unit of gestalt that will detect
;; things extractable by the projection.
(define (projection->gestalt pr)
  (simple-gestalt (not (projection-get-advertisements? pr))
		  (projection->pattern (projection-spec pr))
		  (+ (projection-level pr) 1)
		  (projection-metalevel pr)))

;; Gestalt × Nat × Nat × Boolean × CompiledProjection → Matcher
;; Retrieves the Matcher within g projected by the arguments.
(define (gestalt-project* g metalevel level get-advertisements? capture-spec)
  (define extract-matcher (if get-advertisements? cdr car))
  (define l (safe-list-ref (gestalt-metalevel-ref g metalevel) level (lambda () empty-level)))
  (matcher-project (extract-matcher l) capture-spec))

;; Gestalt × GestaltProjection → Matcher
;; Retrieves the Matcher within g projected by pr.
(define (gestalt-project g pr)
  (match-define (projection metalevel level get-advertisements? _ capture-spec) pr)
  (gestalt-project* g metalevel level get-advertisements? capture-spec))

;; Gestalt × GestaltProjection → (Option (Setof (Listof Value)))
;; Projects g with pr and calls matcher-key-set on the result.
(define (gestalt-project/keys g pr)
  (check-projection-result g pr (matcher-key-set (gestalt-project g pr))))

;; Gestalt × GestaltProjection → (Option (Setof Value))
;; Projects g with pr and calls matcher-key-set/single on the result.
(define (gestalt-project/single g pr)
  (check-projection-result g pr (matcher-key-set/single (gestalt-project g pr))))

;; Gestalt × GestaltProjection × (Option A) → (Option A)
(define (check-projection-result g pr result)
  (when (not result)
    (match-define (projection metalevel level get-advertisements? spec _) pr)
    (log-warning "Wildcard detected projecting ~a at metalevel ~a, level ~a\nwith pattern ~v from gestalt:\n~a"
		 (if get-advertisements? "advs" "subs")
		 metalevel
		 level
		 spec
		 (gestalt->pretty-string g)))
  result)

;; Gestalt -> Gestalt
;; Discards the 0th metalevel, renumbering others appropriately.
;; Used to map a Gestalt from a World to Gestalts of its containing World.
(define (drop-gestalt g)
  (gestalt (safe-cdr (gestalt-metalevels g))))

;; Gestalt -> Gestalt
;; Adds a fresh empty 0th metalevel, renumbering others appropriately.
;; Used to map Gestalt from a World's container to the World's own Gestalt.
(define (lift-gestalt g)
  (gestalt (cons-metalevel empty-metalevel (gestalt-metalevels g))))

;; Nat X (Listof X) -> (Listof X)
;; Prepends n references to x to xs.
(define (prepend n x xs)
  (if (zero? n)
      xs
      (cons x (prepend (- n 1) x xs))))

;; Boolean Pattern Nat Nat -> Gestalt
;; Compiles p and embeds it at the appropriate level and metalevel
;; within a Gestalt. Used by (pub) and (sub) to construct "atomic"
;; Gestalts.
(define (simple-gestalt is-adv? p level metalevel)
  (define m (pattern->matcher #t p))
  (define pom (if is-adv? (cons #f m) (cons m #f)))
  (gestalt (prepend metalevel empty-metalevel (list (prepend level empty-level (list pom))))))

;; -> Gestalt
;; The empty gestalt.
(define (gestalt-empty) (gestalt '()))

;; Gestalt -> Boolean
;; True iff the gestalt matches no messages.
;; TODO: our invariants should ensure that (gestalt-empty? g) iff (equal? g (gestalt '())).
;;       Make sure this actually is true.
(define (gestalt-empty? g)
  (for*/and [(ml (in-list (gestalt-metalevels g))) (l (in-list ml))]
    (and (matcher-empty? (car l)) (matcher-empty? (cdr l)))))

;; Nat Nat -> GestaltSet
;; Produces a "full" gestalt including the wildcard matcher at each of
;; the n metalevels and m levels.
(define (gestalt-full n m)
  (define w (pattern->matcher #t ?))
  (gestalt (make-list n (make-list m (cons w w)))))

;; map-zip: ((U 'right-longer 'left-longer) (Listof X) -> (Listof Y))
;;          (X X -> Y)
;;          (Y (Listof Y) -> (Listof Y))
;;          (Listof X)
;;          (Listof X)
;;       -> (Listof Y)
;; Horrific map-like function that isn't quite as picky as map about
;; ragged input lists. The imbalance-handler is used to handle ragged
;; inputs.
(define (map-zip imbalance-handler item-handler gcons ls1 ls2)
  (let walk ((ls1 ls1) (ls2 ls2))
    (match* (ls1 ls2)
      [('() '()) '()]
      [('() ls) (imbalance-handler 'right-longer ls)]
      [(ls '()) (imbalance-handler 'left-longer ls)]
      [((cons l1 ls1) (cons l2 ls2))
       (gcons (item-handler l1 l2) (walk ls1 ls2))])))

;; Gestalt Gestalt (...->...) (Level Level -> Level) -> Gestalt
;; Combine two gestalts with the given level-combiner.
;; The type of imbalance-handler is awkward because of the punning.
(define (gestalt-combine g1 g2 imbalance-handler level-combiner)
  (gestalt (map-zip imbalance-handler
		    (lambda (ls1 ls2)
		      (map-zip imbalance-handler level-combiner cons-level ls1 ls2))
		    cons-metalevel
		    (gestalt-metalevels g1)
		    (gestalt-metalevels g2))))

;; Gestalt Gestalt (...->...) (Matcher Matcher -> Matcher) -> Gestalt
;; Combines g1 and g2, giving subs/subs and advs/advs from g1 and g2
;; to the matcher-combiner.
(define (gestalt-combine-straight g1 g2 imbalance-handler matcher-combiner)
  (gestalt-combine g1 g2
		   imbalance-handler
		   (lambda (sa1 sa2)
		     (cons (matcher-combiner (car sa1) (car sa2))
			   (matcher-combiner (cdr sa1) (cdr sa2))))))

;; (Listof Gestalt) -> Gestalt
;; Computes the union of the given gestalts.
(define (gestalt-union* gs)
  (if (null? gs)
      (gestalt-empty)
      (let walk ((gs gs))
	(match gs
	  [(list g) g]
	  [(cons g rest) (gestalt-union1 g (walk rest))]))))

;; Gestalt* -> Gestalt
;; Computes the union of its arguments.
(define (gestalt-union . gs)
  (gestalt-union* gs))

;; Gestalt Gestalt -> Gestalt
;; Computes the union of its arguments.
(define (gestalt-union1 g1 g2) (gestalt-combine-straight g1 g2 (lambda (side x) x) matcher-union))

;; TODO: abstract out the folding skeletons of gestalt-filter and gestalt-match.

;; Gestalt Gestalt -> Gestalt
;; View on g1 from g2's perspective.
;; Implements the "(p)_n || <p>_m if n < m" part of NC.
(define gestalt-filter
  (let ()
    (define (filter-metalevels mls1 mls2)
      (match* (mls1 mls2)
	[('() _) '()]
	[(_ '()) '()]
	[((cons ls1 mrest1) (cons ls2-unshifted mrest2))
	 (cons-metalevel (filter-levels ls1 (safe-cdr ls2-unshifted))
			 (filter-metalevels mrest1 mrest2))]))

    (define (filter-levels ls1 ls2)
      (match ls1
	['() '()]
	[(cons (cons subs1 advs1) lrest1)
	 (if (null? ls2)
	     '()
	     (cons-level (filter-single-level subs1 advs1 ls2)
			 (filter-levels lrest1 (cdr ls2))))]))

    (define (filter-single-level subs1 advs1 ls2)
      (let loop ((ls2 ls2) (subs #f) (advs #f))
	(match ls2
	  ['() (cons subs advs)]
	  [(cons (cons subs2 advs2) lrest2)
	   (loop lrest2
		 (matcher-union subs (matcher-intersect subs1 advs2))
		 (matcher-union advs (matcher-intersect advs1 subs2)))])))

    (lambda (g1 g2)
      (parameterize ((matcher-intersect-successes (lambda (v1 v2) v1)))
	(gestalt (filter-metalevels (gestalt-metalevels g1) (gestalt-metalevels g2)))))))

;; Gestalt Gestalt -> (Setof PID)
;; Much like gestalt-filter, takes a view on gestalt g1 from g2's
;; perspective. However, instead of returning the filtered g1, returns
;; just the set of values in the g2-map that were overlapped by some
;; part of g1.
(define gestalt-match
  (let ()
    (define (match-metalevels mls1 mls2 acc)
      (match* (mls1 mls2)
	[('() _) acc]
	[(_ '()) acc]
	[((cons ls1 mrest1) (cons ls2-unshifted mrest2))
	 (match-levels ls1 (safe-cdr ls2-unshifted) (match-metalevels mrest1 mrest2 acc))]))

    (define (match-levels ls1 ls2 acc)
      (match ls1
	['() acc]
	[(cons (cons subs1 advs1) lrest1)
	 (if (null? ls2)
	     acc
	     (match-single-level subs1 advs1 ls2 (match-levels lrest1 (cdr ls2) acc)))]))

    (define (match-single-level subs1 advs1 ls2 acc)
      (let loop ((ls2 ls2) (acc acc))
	(match ls2
	  ['() acc]
	  [(cons (cons subs2 advs2) lrest2)
	   (loop lrest2 (tset-union (tset-union (matcher-match-matcher subs1 advs2)
                                                (matcher-match-matcher advs1 subs2))
                                    acc))])))

    (lambda (g1 g2)
      (parameterize ((matcher-match-matcher-successes (lambda (v1 v2 acc) (tset-union v2 acc)))
		     (matcher-match-matcher-unit (datum-tset)))
	(match-metalevels (gestalt-metalevels g1) (gestalt-metalevels g2) (datum-tset))))))

;; Gestalt Gestalt -> Gestalt
;; Erases the g2-subset of g1 from g1, yielding the result.
(define (gestalt-subtract g1 g2)
  (gestalt-combine-straight g1 g2
			    erase-imbalance-handler
			    matcher-subtract))

;; (U 'right-longer 'left-longer) (Listof X) -> (Listof X)
;; Asymmetric imbalance handler suitable for use in subtraction operations.
(define (erase-imbalance-handler side x)
  (case side
    [(left-longer) x]
    [(right-longer) '()]))

;; Gestalt (Nat Nat Level -> Level) -> Gestalt
;; Maps f over all levels in g, passing f the metalevel number, the
;; level number, and the level itself, in that order.
(define (gestalt-transform g f)
  (gestalt (let loop-outer ((mls (gestalt-metalevels g)) (i 0))
	     (cond [(null? mls) '()]
		   [else (cons-metalevel
			  (let loop-inner ((ls (car mls)) (j 0))
			    (cond [(null? ls) '()]
				  [else (cons-level (f i j (car ls))
						    (loop-inner (cdr ls) (+ j 1)))]))
			  (loop-outer (cdr mls) (+ i 1)))]))))

;; Gestalt (Matcher -> Matcher) -> Gestalt
;; Maps f over all matchers in g.
(define (gestalt-matcher-transform g f)
  (gestalt-transform g (lambda (i j p) (cons (f (car p)) (f (cdr p))))))

;; Gestalt -> GestaltSet
;; Blurs the distinctions between mapped-to processes in g.
(define (strip-gestalt-label g)
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (v) #t)))))

;; GestaltSet -> Gestalt
;; Relabels g so that all matched keys map to (set pid).
(define (label-gestalt g pid)
  (define pidset (datum-tset pid))
  (gestalt-matcher-transform g (lambda (m) (matcher-relabel m (lambda (v) pidset)))))

;; Gestalt Nat -> Nat
;; Returns the number of "interesting" levels in g at metalevel n.
(define (gestalt-level-count g n)
  (length (gestalt-metalevel-ref g n)))

;; Gestalt [OutputPort] -> Void
;; Pretty-prints g on port.
(define (pretty-print-gestalt g [port (current-output-port)])
  (if (gestalt-empty? g)
      (fprintf port "EMPTY GESTALT\n")
      (for [(metalevel (in-naturals)) (ls (in-list (gestalt-metalevels g)))]
	(for [(level (in-naturals)) (p (in-list ls))]
	  (match-define (cons subs advs) p)
	  (when (or subs advs)
	    (fprintf port "GESTALT metalevel ~v level ~v:\n" metalevel level)
	    (when subs (fprintf port "  - subs:") (pretty-print-matcher subs port #:indent 9))
	    (when advs (fprintf port "  - advs:") (pretty-print-matcher advs port #:indent 9)))))))

;; Gestalt -> String
;; Returns a string containing the pretty-printing of g.
(define (gestalt->pretty-string g)
  (with-output-to-string (lambda () (pretty-print-gestalt g))))

;; Gestalt [(Value -> JSExpr)] -> JSExpr
;; Serializes a gestalt to a JSON expression.
(define (gestalt->jsexpr g [success->jsexpr (lambda (v) #t)])
  (list "gestalt" (for/list [(ls (in-list (gestalt-metalevels g)))]
		    (for/list [(l (in-list ls))]
		      (match-define (cons subs advs) l)
		      (list (matcher->jsexpr subs success->jsexpr)
			    (matcher->jsexpr advs success->jsexpr))))))

;; JSExpr [(JSExpr -> Value)] -> Gestalt
;; Deserializes a gestalt from a JSON expression.
(define (jsexpr->gestalt j [jsexpr->success (lambda (v) #t)])
  (match j
    [(list "gestalt" mlsj)
     (gestalt (for/list [(lsj (in-list mlsj))]
		(for/list [(lj (in-list lsj))]
		  (match-define (list sj aj) lj)
		  (cons (jsexpr->matcher sj jsexpr->success)
			(jsexpr->matcher aj jsexpr->success)))))]))

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
					   (pattern->matcher #t 'b))))))

  (require json)
  (let ((J (string->jsexpr "[\"gestalt\",[[[[[\"A\",[[[\")\"],[\"\",true]]]]],[]]],[],[[[],[]],[[],[]],[[],[[\"B\",[[[\")\"],[\"\",true]]]]]]]]]"))
	(G (gestalt-union (simple-gestalt #f "A" 0 0) (simple-gestalt #t "B" 2 2))))
    (check-equal? (jsexpr->gestalt J (lambda (v) v)) G)
    (check-equal? (gestalt->jsexpr G (lambda (v) v)) J)))
