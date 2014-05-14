#lang racket/base

(require racket/set)
(require racket/match)
(require (only-in racket/port call-with-output-string))
(require (only-in racket/class object?))

(require rackunit)

(provide ?
	 wildcard?
	 ?!
	 capture?
	 pattern->matcher
	 matcher? ;; expensive; see implementation
	 matcher-empty
	 matcher-empty?
	 matcher-union
	 matcher-intersect
	 matcher-erase-path
	 matcher-match-value
	 matcher-match-matcher
	 matcher-relabel
	 compile-projection
	 matcher-project
	 matcher->finite-set
	 pretty-print-matcher)

(define-syntax-rule (define-singleton-struct singleton-name struct-name print-representation)
  (begin
    (struct struct-name ()
	    #:transparent
	    #:property prop:custom-write
	    (lambda (v port mode) (display print-representation port)))
    (define singleton-name (struct-name))))

;; Unicode angle brackets: 〈, 〉

;; A Sigma is, roughly, a token in a value being matched. It is one of:
;;  - a struct-type, signifying the start of a struct.
;;  - start-of-pair, signifying the start of a pair.
;;  - start-of-vector, signifying the start of a vector.
;;  - end-of-sequence, signifying the notional close-paren at the end of a compound.
;;  - any other value, representing itself.
(define-singleton-struct SOP start-of-pair "<pair")
(define-singleton-struct SOV start-of-vector "<vector")
(define-singleton-struct EOS end-of-sequence ">")

;; A Pattern is an atom, the special wildcard value, or a Racket
;; compound (struct, pair, or vector) containing Patterns.
(define-singleton-struct ? wildcard "★") ;; alternative printing: ¿

;; When projecting a matcher, the capturing wildcard can be used.
(define-singleton-struct ?! capture "‽")

;; A Matcher is either
;; - #f, indicating no further matches possible
;; - a Set of Any, representing a successful match (if the end of the input has been reached)
;; - a Hashtable mapping (Sigma or wildcard) to Matcher
;; - a (wildcard-sequence Matcher)
;; If, in a hashtable matcher, a wild key is present, it is intended
;; to catch all and ONLY those keys not otherwise present in the
;; table.
(struct wildcard-sequence (matcher) #:transparent)

(define (matcher? x)
  (or (eq? x #f)
      (set? x)
      (wildcard-sequence? x)
      (and (hash? x)
	   (for/and ([v (in-hash-values x)])
	     (matcher? v)))))

(define (matcher-empty) #f)
(define (matcher-empty? r) (not r))

(define (rvalue v) (set v))

(define (rseq e r)   (if (matcher-empty? r) r (hash e r)))
(define (rwild r)    (rseq ? r))
(define (rwildseq r) (if (matcher-empty? r) r (wildcard-sequence r)))

(define (rseq* x . xs)
  (let walk ((xs (cons x xs)))
    (match xs
      [(list r) r]
      [(cons e xs1) (rseq e (walk xs1))])))

;; Any -> Boolean
;; Racket objects are structures, so we reject them explicitly for
;; now, leaving them opaque to unification.
(define (non-object-struct? x)
  (and (struct? x)
       (not (object? x))))

(define (pattern->matcher v p)
  (let walk ((p p) (acc (rseq EOS (rvalue v))))
    (match p
      [(== ?) (rwild acc)]
      [(cons p1 p2) (rseq SOP (walk p1 (walk p2 (rseq EOS acc))))]
      [(vector ps ...) (rseq SOV (foldr walk (rseq EOS acc) ps))]
      [(? non-object-struct?)
       (define-values (t skipped?) (struct-info p))
       (when skipped? (error 'pattern->matcher "Cannot reflect on struct instance ~v" p))
       (define fs (cdr (vector->list (struct->vector p))))
       (rseq t (foldr walk (rseq EOS acc) fs))]
      ;; TODO: consider options for treating hash tables as compounds rather than (useless) atoms
      [(? hash?) (error 'pattern->matcher "Cannot match on hash tables at present")]
      [other (rseq other acc)])))

(define (rlookup r key)
  (hash-ref r key (lambda () #f)))

(define (rupdate r key k)
  (if (matcher-empty? k)
      (and r (hash-remove r key))
      (hash-set (or r (hash)) key k)))

(define (key-open? k)
  (or (eq? k SOP)
      (eq? k SOV)
      (struct-type? k)))

(define (key-close? k)
  (eq? k EOS))

(define (key-normal? k)
  (not (or (key-open? k)
	   (key-close? k))))

(define (expand-wildseq r)
  (matcher-union (rwild (rwildseq r))
		 (rseq EOS r)))

(define matcher-union
  (let ()
    (define (merge o1 o2)
      (match* (o1 o2)
	[(#f #f) #f]
	[(#f r) r]
	[(r #f) r]
	[(r1 r2) (walk r1 r2)]))
    (define (walk re1 re2)
      (match* (re1 re2)
	[((wildcard-sequence r1) (wildcard-sequence r2)) (rwildseq (walk r1 r2))]
	[((wildcard-sequence r1) r2) (walk (expand-wildseq r1) r2)]
	[(r1 (wildcard-sequence r2)) (walk (expand-wildseq r2) r1)]
	[((? set? v1) (? set? v2)) (set-union v1 v2)]
	[((? hash? h1) (? hash? h2))
	 (define w (merge (rlookup h1 ?) (rlookup h2 ?)))
	 (cond
	  [w (merge/wildcard w h1 h2)]
	  [(< (hash-count h2) (hash-count h1)) (merge/no-wildcard h2 h1)]
	  [else (merge/no-wildcard h1 h2)])]))
    (define (merge/wildcard w h1 h2)
      (for/fold [(acc (rwild w))]
	  [(key (set-remove (set-union (hash-keys h1) (hash-keys h2)) ?))]
	(define k (merge (rlookup h1 key) (rlookup h2 key)))
	(rupdate acc
		 key
		 (cond
		  [(key-open? key) (merge (rwildseq w) k)]
		  [(key-close? key) (if (wildcard-sequence? w)
					(merge (wildcard-sequence-matcher w) k)
					k)]
		  [else (merge w k)]))))
    (define (merge/no-wildcard h1 h2)
      (for/fold [(acc h2)] [((key k1) (in-hash h1))]
	(define k (merge k1 (rlookup h2 key)))
	(rupdate acc key k)))
    (lambda (re1 re2)
      (match* (re1 re2)
	[(#f r) r]
	[(r #f) r]
	[(r1 r2) (walk r1 r2)]))))

(define (matcher-intersect re1 re2 [combine-success-values set-union])
  (let ()
    ;; INVARIANT: re1 is a part of the original re1, and likewise for
    ;; re2. This is so that the first arg to combine-success-values
    ;; always comes from re1, and the second from re2.
    (define (walk re1 re2)
      (match* (re1 re2)
	[((wildcard-sequence r1) (wildcard-sequence r2)) (rwildseq (walk r1 r2))]
	[((wildcard-sequence r1) r2) (walk (expand-wildseq r1) r2)]
	[(r1 (wildcard-sequence r2)) (walk r1 (expand-wildseq r2))]
	[((? set? v1) (? set? v2)) (combine-success-values v1 v2)]
	[((? hash? h1) (? hash? h2))
	 (define w1 (rlookup h1 ?))
	 (define w2 (rlookup h2 ?))
	 (define w (and w1 w2 (walk w1 w2)))
	 ;; TODO: if, say, w1 is #f, then we don't need to examine
	 ;; every key in h2. So there are four cases:
	 ;;  - both false -> examine the intersection of the key sets
	 ;;                  (done by enumerating keys in the smaller hash)
	 ;;  - one nonfalse -> examine only the keys in the other
	 ;;  - both nonfalse -> examine the union of the key sets
	 ;; This is important for avoiding examination of the whole
	 ;; structure when wildcards aren't being used.
	 (for/fold [(acc (rwild w))]
	     [(key (set-remove (set-union (hash-keys h1) (hash-keys h2)) ?))]
	   (rupdate acc
		    key
		    (match* ((rlookup h1 key) (rlookup h2 key))
		      [(#f #f) #f]
		      [(#f k2) (walk-wild                          walk w1 key k2)]
		      [(k1 #f) (walk-wild (lambda (a2 a1) (walk a1 a2)) w2 key k1)]
		      [(k1 k2) (walk k1 k2)])))]))
    (define (walk-wild walk-fn w key k)
      (and w (cond
	      [(key-open? key) (walk-fn (rwildseq w) k)]
	      [(key-close? key) (if (wildcard-sequence? w)
				    (walk-fn (wildcard-sequence-matcher w) k)
				    #f)]
	      [else (walk-fn w k)])))
    (match* (re1 re2)
      [(#f r) #f]
      [(r #f) #f]
      [(r1 r2) (walk r1 r2)])))

;; Removes re1's mappings from re2. Assumes re1 has previously been union'd into re2.
(define matcher-erase-path
  (let ()
    (define (cofinite-pattern)
      (error 'matcher-erase-path "Cofinite pattern required"))
    (define (walk path aggregate)
      (match* (path aggregate)
	[((wildcard-sequence r1) (wildcard-sequence r2)) (rwildseq (walk r1 r2))]
	[((wildcard-sequence r1) r2) (walk (expand-wildseq r1) r2)]
	[(r1 (wildcard-sequence r2)) (cofinite-pattern)]
	[((? set? v1) (? set? v2))
	 (define v (set-subtract v2 v1))
	 (if (set-empty? v) #f v)]
	[((? hash? h1) (? hash? h2))
	 (define w1 (rlookup h1 ?))
	 (define w2 (rlookup h2 ?))
	 (define w (match* (w1 w2)
		     [(#f #f) #f]
		     [(#f r) r]
		     [(r #f) (cofinite-pattern)]
		     [(r1 r2) (walk r1 r2)]))
	 ;; TODO: only need to examine all keys of h2 if w1 nonfalse.
	 ;; TODO: need to ensure "minimal" remainder in cases where
	 ;; after an erasure, a particular key's continuation is the
	 ;; same as the wildcard's continuation. See tests/examples
	 ;; below.
	 (for/fold [(acc (rwild w))]
	     [(key (set-remove (set-union (hash-keys h1) (hash-keys h2)) ?))]
	   (rupdate acc
		    key
		    (match* ((rlookup h1 key) (rlookup h2 key))
		      [(#f #f) #f]
		      [(#f k2) (walk-wild w1 key k2)]
		      [(k1 #f) (cofinite-pattern)]
		      [(k1 k2) (walk k1 k2)])))]))
    (define (walk-wild w key k)
      (if w
	  (cond
	   [(key-open? key) (walk (rwildseq w) k)]
	   [(key-close? key) (if (wildcard-sequence? w)
				 (walk (wildcard-sequence-matcher w) k)
				 k)]
	   [else (walk w k)])
	  k))
    (lambda (re1 re2)
      (match* (re1 re2)
	[(#f r) r]
	[(r #f) (cofinite-pattern)]
	[(r1 r2) (walk r1 r2)]))))

(define (matcher-match-value r v)
  (if (matcher-empty? r)
      (set)
      (let walk ((vs (list v)) (stack '(())) (r r))
	(define (walk-wild vs stack)
	  (match (rlookup r ?)
	    [#f (set)]
	    [k (walk vs stack k)]))
	(match r
	  [(wildcard-sequence k)
	   (match stack
	     ['() (set)]
	     [(cons rest stack1) (walk rest stack1 k)])]
	  [(? set?)
	   (if (and (null? vs)
		    (null? stack))
	       r
	       (set))]
	  [(? hash?)
	   (match vs
	     ['()
	      (match stack
		['() (set)]
		[(cons rest stack1)
		 (match (rlookup r EOS)
		   [#f (set)]
		   [k (walk rest stack1 k)])])]
	     [(cons (== ?) rest)
	      (error 'matcher-match-value "Cannot match wildcard as a value")]
	     [(cons (cons v1 v2) rest)
	      (match (rlookup r SOP)
		[#f (walk-wild rest stack)]
		[k (walk (list v1 v2) (cons rest stack) k)])]
	     [(cons (vector vv ...) rest)
	      (match (rlookup r SOV)
		[#f (walk-wild rest stack)]
		[k (walk vv (cons rest stack) k)])]
	     [(cons (? non-object-struct? s) rest)
	      (define-values (t skipped?) (struct-info s))
	      (when skipped? (error 'matcher-match-value "Cannot reflect on struct instance ~v" s))
	      (define fs (cdr (vector->list (struct->vector s))))
	      (match (rlookup r t)
		[#f (walk-wild rest stack)]
		[k (walk fs (cons rest stack) k)])]
	     [(cons v rest)
	      (match (rlookup r v)
		[#f (walk-wild rest stack)]
		[k (walk rest stack k)])])]))))

(define (matcher-match-matcher re1 re2)
  (let ()
    (define (walk re1 re2 acc1 acc2)
      (match* (re1 re2)
	[((wildcard-sequence r1) (wildcard-sequence r2)) (walk r1 r2 acc1 acc2)]
	[((wildcard-sequence r1) r2) (walk (expand-wildseq r1) r2 acc1 acc2)]
	[(r1 (wildcard-sequence r2)) (walk r1 (expand-wildseq r2) acc1 acc2)]
	[((? set? v1) (? set? v2)) (values (set-union acc1 v1) (set-union acc2 v2))]
	[((? hash? h1) (? hash? h2))
	 (define w1 (rlookup h1 ?))
	 (define w2 (rlookup h2 ?))
	 (define-values (r1 r2) (if (and w1 w2)
				    (walk w1 w2 acc1 acc2)
				    (values acc1 acc2)))
	 ;; TODO: optimize as described in matcher-intersect.
	 (for/fold [(r1 r1)
		    (r2 r2)]
	     [(key (set-remove (set-union (hash-keys h1) (hash-keys h2)) ?))]
	   (match* ((rlookup h1 key) (rlookup h2 key))
		      [(#f #f) (values r1 r2)]
		      [(#f k2)
		       (define-values (rr1 rr2) (walk-wild w1 key k2 r1 r2))
		       (values rr1 rr2)]
		      [(k1 #f)
		       (define-values (rr2 rr1) (walk-wild w2 key k1 r2 r1))
		       (values rr1 rr2)]
		      [(k1 k2) (walk k1 k2 r1 r2)]))]))
    (define (walk-wild w key k acc1 acc2)
      (if w
	  (cond
	   [(key-open? key) (walk (rwildseq w) k acc1 acc2)]
	   [(key-close? key) (if (wildcard-sequence? w)
				 (walk (wildcard-sequence-matcher w) k acc1 acc2)
				 #f)]
	   [else (walk w k acc1 acc2)])
	  (values acc1 acc2)))
    (match* (re1 re2)
      [(#f r) (values (set) (set))]
      [(r #f) (values (set) (set))]
      [(r1 r2) (walk r1 r2 (set) (set))])))

(define (matcher-relabel m f)
  (let walk ((m m))
    (match m
      [#f #f]
      [(? set?) (f m)]
      [(wildcard-sequence m1) (wildcard-sequence (walk m1))]
      [(? hash?) (for/hash [((k v) (in-hash m))] (values k (walk v)))])))

(define (compile-projection p)
  ;; Extremely similar to pattern->matcher. Besides use of conses
  ;; rather than chained hashtables, the only interesting difference
  ;; is how ?! is treated.
  (let walk ((p p) (acc (cons EOS '())))
    (match p
      [(== ?!) (cons ?! acc)]
      [(== ?) (cons ? acc)]
      [(cons p1 p2) (cons SOP (walk p1 (walk p2 (cons EOS acc))))]
      [(vector ps ...) (cons SOV (foldr walk (cons EOS acc) ps))]
      [(? non-object-struct?)
       (define-values (t skipped?) (struct-info p))
       (when skipped? (error 'pattern->matcher "Cannot reflect on struct instance ~v" p))
       (define fs (cdr (vector->list (struct->vector p))))
       (cons t (foldr walk (cons EOS acc) fs))]
      ;; TODO: consider options for treating hash tables as compounds rather than (useless) atoms
      [(? hash?) (error 'pattern->matcher "Cannot match on hash tables at present")]
      [other (cons other acc)])))

;; Matcher × CompiledProjection → Matcher
;; The result matches a vector of length equal to the number of captures.
(define matcher-project
  ;; TODO: skip-nested, capture-nested, and the ? and ?! cases in
  ;; walk-out all share a suspicious amount of code. Refactor it away.
  (let ()
    (define (skip-nested m k)
      (match m
	[(wildcard-sequence mk) (k mk)]
	[(? hash?)
	 (for/fold [(acc (skip-nested (rlookup m ?) k))] [((key mk) (in-hash m))]
	   (if (eq? key ?)
	       acc
	       (matcher-union acc (cond
				   [(key-open? key) (skip-nested mk (lambda (mk) (skip-nested mk k)))]
				   [(key-close? key) (k mk)]
				   [else (skip-nested mk k)]))))]
	[_ (matcher-empty)]))

    (define (capture-nested m k)
      (match m
	[(wildcard-sequence mk) (rwildseq (k mk))]
	[(? hash?)
	 (for/fold [(acc (rwild (capture-nested (rlookup m ?) k)))] [((key mk) (in-hash m))]
	   (if (eq? key ?)
	       acc
	       (cond
		[(key-open? key)
		 (rupdate acc key (capture-nested mk (lambda (mk) (capture-nested mk k))))]
		[(key-close? key) (rupdate acc key (k mk))]
		[else (rupdate acc key (capture-nested mk k))])))]
	[_ (matcher-empty)]))

    (define (walk-out m spec)
      (match spec
	['()
	 (match m
	   [(? set?) (rseq EOS (rseq EOS (set #t)))]
	   ;; ^ the #t yields a matcher that does not preserve map values.
	   [_ (matcher-empty)])]

	[(cons (== ?) k)
	 (match m
	   [(wildcard-sequence _) (walk-out m k)]
	   [(? hash?)
	    (for/fold [(acc (walk-out (rlookup m ?) k))] [((key mk) (in-hash m))]
	      (if (eq? key ?)
		  acc
		  (matcher-union acc (cond
				      [(key-open? key) (skip-nested mk (lambda (mk) (walk-out mk k)))]
				      [(key-close? key) #f]
				      [else (walk-out mk k)]))))]
	   [_ (matcher-empty)])]

	[(cons (== ?!) k)
	 (match m
	   [(wildcard-sequence _) (rwild (walk-out m k))]
	   [(? hash?)
	    (for/fold [(acc (rwild (walk-out (rlookup m ?) k)))] [((key mk) (in-hash m))]
	      (if (eq? key ?)
		  acc
		  (cond
		   [(key-open? key)
		    (rupdate acc key (capture-nested mk (lambda (mk) (walk-out mk k))))]
		   [(key-close? key) acc]
		   [else (rupdate acc key (walk-out mk k))])))]
	   [_ (matcher-empty)])]

	[(cons sigma k)
	 (match m
	   [(wildcard-sequence mk)
	    (if (key-close? sigma)
		(walk-out mk k)
		(walk-out m k))]
	   [(? hash?)
	    (matcher-union (walk-out (rlookup m sigma) k)
			   (walk-out (rlookup m ?) k))]
	   [_ (matcher-empty)])]))

    (lambda (m spec)
      (rseq SOV (walk-out m spec)))))

;; Matcher → (Option (Setof Value))
;; Multiplies out unions. Returns #f if any dimension of m is infinite.
(define matcher->finite-set
  (let ()
    ;; Matcher (Value Matcher -> (Setof Value)) -> (Option (Setof Value))
    ;; Calls k with each possible atomic value at this matcher
    ;; position, and accumulates the results.
    (define (walk m k)
      (match m
	[(wildcard-sequence _) #f]
	[(? hash?)
	 (and (not (hash-has-key? m ?))
	      (for/fold [(acc (set))] [((key mk) (in-hash m))]
		(maybe-union
		 acc
		 (cond
		  [(key-open? key)
		   (walk-seq mk (lambda (vss vsk)
				  (for/fold [(acc (set))] [(vs (in-set vss))]
				    (maybe-union acc
						 (k (transform-seqs vs key) vsk)))))]
		  [(key-close? key)
		   (error 'matcher->finite-set "Internal error: unexpected key-close")]
		 [else
		  (k key mk)]))))]
	[_ (set)]))

    ;; Matcher (Value Matcher -> (Setof (Listof Value))) -> (Option (Setof (Listof Value)))
    ;; Calls k with each possible sequence of atomic values at this
    ;; matcher position, and accumulates the results.
    (define (walk-seq m k)
      (match m
	[(wildcard-sequence _) #f]
	[(? hash?)
	 (and (not (hash-has-key? m ?))
	      (for/fold [(acc (set))] [((key mk) (in-hash m))]
		(maybe-union acc (cond
				  [(key-close? key) (k (set '()) mk)]
				  [else (walk (rseq key mk)
					      (lambda (v vk)
						(walk-seq vk (lambda (vss vsk)
							       (k (for/set [(vs (in-set vss))]
								    (cons v vs))
								  vsk)))))]))))]
	[_ (k (set) #f)])) ;; TODO: ??

    ;; (Listof Value) Sigma -> Value
    (define (transform-seqs vs opener)
      (cond
       [(eq? opener SOP) (apply cons vs)]
       [(eq? opener SOV) (list->vector vs)]
       [(struct-type? opener) (apply (struct-type-make-constructor opener) vs)]))

    ;; (Option (Setof A)) (Option (Setof A)) -> (Option (Setof A))
    (define (maybe-union s1 s2) (and s1 s2 (set-union s1 s2)))

    (lambda (m)
      (walk m (lambda (v k) (set v))))))

(define (pretty-print-matcher m [port (current-output-port)] #:indent [initial-indent 0])
  (define (d x) (display x port))
  (define (walk i m)
    (match m
      [#f
       (d "::: no further matches possible")]
      [(wildcard-sequence k)
       (d "...>")
       (walk (+ i 4) k)]
      [(? set? vs)
       (d "{")
       (for ((v vs)) (d v))
       (d "}")]
      [(? hash? h)
       (if (zero? (hash-count h))
	   (d " ::: empty hash!")
	   (for/fold [(need-sep? #f)] [((key k) (in-hash h))]
	     (when need-sep?
	       (newline port)
	       (d (make-string i #\space)))
	     (d " ")
	     (define keystr (call-with-output-string
			     (lambda (p)
			       (if (struct-type? key)
				   (let-values (((name x2 x3 x4 x5 x6 x7 x8)
						 (struct-type-info key)))
				     (display "<s:" p)
				     (display name p))
				   (display key p)))))
	     (d keystr)
	     (walk (+ i 1 (string-length keystr)) k)
	     #t))]))
  (walk initial-indent m)
  (newline port)
  m)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (define (E . vs) (hash EOS (apply set vs)))
  (check-equal? (pattern->matcher 'A 123) (hash 123 (E 'A)))
  (check-equal? (pattern->matcher 'A (cons 1 2)) (hash SOP (hash 1 (hash 2 (hash EOS (E 'A))))))
  (check-equal? (pattern->matcher 'A (cons ? 2)) (hash SOP (hash ? (hash 2 (hash EOS (E 'A))))))
  (check-equal? (pattern->matcher 'A SOP) (hash struct:start-of-pair (hash EOS (E 'A))))
  (check-equal? (pattern->matcher 'A ?) (hash ? (E 'A)))
  )

(module+ test
  (define (check-matches matcher . tests)
    (let walk ((tests tests))
      (match tests
	['() (void)]
	[(list* message expectedstr rest)
	 (define actualset (matcher-match-value matcher message))
	 (printf "~v ==> ~v\n" message actualset)
	 (check-equal? actualset
		       (apply set (map (lambda (c) (string->symbol (string c)))
				       (string->list expectedstr))))
	 (walk rest)])))

  (check-matches
   #f
   (list 'z 'x) ""
   'foo ""
   (list (list 'z (list 'z))) "")

  (define (pretty-print-matcher* m)
    (newline)
    (pretty-print-matcher m)
    (flush-output))
 
  (void (pretty-print-matcher*
	 (matcher-union (pattern->matcher 'A (list (list ?) 'x))
			(pattern->matcher 'B (list (list ?) 'y)))))

  (void (pretty-print-matcher*
	 (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
			(pattern->matcher 'B (list (list 'c 'd) 'y)))))

  (void (pretty-print-matcher*
	 (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
			(pattern->matcher 'B (list (list  ?  ?) 'y)))))

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
		   (pattern->matcher 'B (list (list  ?  ?) 'x))))
   (list 'z 'x) ""
   (list (list 'z 'z) 'x) "B"
   (list (list 'z (list 'z)) 'x) "B"
   (list (list 'a 'b) 'x) "AB")

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
		   (pattern->matcher 'B (list (list ?)     'y))))
   (list 'z 'y) ""
   (list (list 'z 'z) 'y) ""
   (list (list 'z 'z) 'x) ""
   (list (list 'a 'b) 'x) "A")

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
		   (pattern->matcher 'B (list ? 'y))))
   (list 'z 'y) "B"
   (list (list 'z 'z) 'y) "B"
   (list (list 'a 'b) 'x) "A")

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list 'a 'b))
		   (pattern->matcher 'B (list 'c 'd))))
   (list 'a 'b) "A"
   (list 'c 'd) "B"
   (list 'a 'd) ""
   (list 'c 'b) "")

  (void (pretty-print-matcher* (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
					      ;; Note: this is a largely nonsense matcher,
					      ;; since it expects no input at all
					      (rseq EOS (rvalue 'B)))))

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list (list 'a 'b) 'x))
		   (pattern->matcher 'B ?)))
   (list (list 'a 'b) 'x) "AB"
   'p "B"
   (list 'p) "B")

  (check-matches
   (pretty-print-matcher*
    (matcher-union (pattern->matcher 'A (list 'a ?))
		   (pattern->matcher 'B (list 'a (list 'b)))))

   (list 'a (list 'b)) "AB"
   (list 'a (list 'b 'b)) "A"
   (list 'a (list 'c 'c)) "A"
   (list 'a (list 'c)) "A"
   (list 'a (list (list))) "A"
   (list 'a (list)) "A"
   (list 'a 'x) "A")

  (check-matches
   (pretty-print-matcher*
    (matcher-union (matcher-union (pattern->matcher 'A (list 'a ?))
				  (pattern->matcher 'A (list 'q ?)))
		   (pattern->matcher 'B (list 'a (list 'b)))))
   (list 'a (list 'b)) "AB"
   (list 'q (list 'b)) "A"
   (list 'a 'x) "A"
   (list 'q 'x) "A"
   (list 'a (list)) "A"
   (list 'q (list)) "A"
   (list 'z (list)) "")

  (define (bigdemo)
    (define ps
      (for/list ((c (in-string "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")))
	(define csym (string->symbol (string c)))
	(pattern->matcher csym (list csym ?))))
    (matcher-union (foldr matcher-union (matcher-empty) ps)
		   (pattern->matcher '+ (list 'Z (list ? '- ?)))))

  (void (pretty-print-matcher* (bigdemo)))
  (check-matches
   (bigdemo)
   (list 'a '-) "a"
   (list 'Z '-) "Z"
   (list '? '-) ""
   (list 'a (list '- '- '-)) "a"
   (list 'a (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "a"
   (list 'Z) ""
   (list 'Z 'x) "Z"
   (list 'Z (list)) "Z"
   (list 'Z (list '-)) "Z"
   (list 'Z (list '-)) "Z"
   (list 'Z (list '- '-)) "Z"
   (list 'Z (list '- '- '-)) "Z+"
   (list 'Z (list '- '- '- '-)) "Z"
   (list 'Z (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "Z"
   (list 'Z '((()) - -)) "Z+"
   (list '? (list '- '- '-)) "")

  (check-matches (pretty-print-matcher* (pattern->matcher 'A (list* 'a 'b ?)))
		 (list 'a 'b 'c 'd 'e 'f) "A"
		 (list 'b 'c 'd 'e 'f 'a) ""
		 3 "")

  (void (pretty-print-matcher* (matcher-intersect (pattern->matcher 'A (list 'a))
						  (pattern->matcher 'B (list 'b)))))

  (let ((r1 (matcher-union (pattern->matcher 'A (list  ? 'b))
			   (pattern->matcher 'A (list  ? 'c))))
	(r2 (matcher-union (pattern->matcher 'B (list 'a  ?))
			   (pattern->matcher 'B (list 'b  ?)))))
    (pretty-print-matcher* (matcher-union r1 r2))
    (pretty-print-matcher* (matcher-union r1 r1))
    (pretty-print-matcher* (matcher-union r2 r2))
    (pretty-print-matcher* (matcher-intersect r1 r2))
    (pretty-print-matcher* (matcher-intersect r1 r1))
    (pretty-print-matcher* (matcher-intersect r2 r2))
    (void))

  (void (pretty-print-matcher* (matcher-intersect (bigdemo) (pattern->matcher 'X (list 'm 'n)))))

  (check-matches
   (pretty-print-matcher* (matcher-intersect (bigdemo) (pattern->matcher 'X (list 'Z ?))))
   (list 'a '-) ""
   (list 'Z '-) "XZ"
   (list '? '-) ""
   (list 'a (list '- '- '-)) ""
   (list 'a (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) ""
   (list 'Z) ""
   (list 'Z 'x) "XZ"
   (list 'Z (list)) "XZ"
   (list 'Z (list '-)) "XZ"
   (list 'Z (list '-)) "XZ"
   (list 'Z (list '- '-)) "XZ"
   (list 'Z (list '- '- '-)) "XZ+"
   (list 'Z (list '- '- '- '-)) "XZ"
   (list 'Z (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "XZ"
   (list 'Z '((()) - -)) "XZ+"
   (list '? (list '- '- '-)) "")

  (check-matches
   (pretty-print-matcher* (matcher-intersect (bigdemo) (pattern->matcher 'X (list 'Z ?))
					     (lambda (a b) b)))
   (list 'a '-) ""
   (list 'Z '-) "X"
   (list '? '-) ""
   (list 'a (list '- '- '-)) ""
   (list 'a (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) ""
   (list 'Z) ""
   (list 'Z 'x) "X"
   (list 'Z (list)) "X"
   (list 'Z (list '-)) "X"
   (list 'Z (list '-)) "X"
   (list 'Z (list '- '-)) "X"
   (list 'Z (list '- '- '-)) "X"
   (list 'Z (list '- '- '- '-)) "X"
   (list 'Z (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "X"
   (list 'Z '((()) - -)) "X"
   (list '? (list '- '- '-)) "")

  (check-matches
   (pretty-print-matcher* (matcher-intersect (bigdemo) (pattern->matcher 'X ?)
					     (lambda (a b) b)))
   (list 'a '-) "X"
   (list 'Z '-) "X"
   (list '? '-) ""
   (list 'a (list '- '- '-)) "X"
   (list 'a (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "X"
   (list 'Z) ""
   (list 'Z 'x) "X"
   (list 'Z (list)) "X"
   (list 'Z (list '-)) "X"
   (list 'Z (list '-)) "X"
   (list 'Z (list '- '-)) "X"
   (list 'Z (list '- '- '-)) "X"
   (list 'Z (list '- '- '- '-)) "X"
   (list 'Z (list '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '- '-)) "X"
   (list 'Z '((()) - -)) "X"
   (list '? (list '- '- '-)) "")

  (let* ((r1 (pattern->matcher 'A (list  ? 'b)))
	 (r2 (pattern->matcher 'B (list 'a  ?)))
	 (r12 (matcher-union r1 r2)))
    (printf "\n-=-=-=-=-=-=-=-=- erase1\n")
    (pretty-print-matcher* r1)
    (pretty-print-matcher* r2)
    (pretty-print-matcher* r12)
    ;; TODO: these next two are not currently "minimal"
    (pretty-print-matcher* (matcher-erase-path r1 r12))
    (pretty-print-matcher* (matcher-erase-path r2 r12))
    (void))

  (let* ((r1 (matcher-union (pattern->matcher 'A (list 'a ?))
			    (pattern->matcher 'A (list 'b ?))))
	 (r2 (pattern->matcher 'B (list 'b ?)))
	 (r12 (matcher-union r1 r2)))
    (printf "\n-=-=-=-=-=-=-=-=- erase2\n")
    (pretty-print-matcher* r12)
    (pretty-print-matcher* (matcher-erase-path r1 r12))
    (pretty-print-matcher* (matcher-erase-path r2 r12))
    (void))

  )

(module+ test
  (struct a (x) #:prefab)
  (struct b (x) #:transparent)

  (define (intersect a b)
    (matcher-intersect (pattern->matcher 'A a)
		       (pattern->matcher 'B b)))

  (define EAB (E 'A 'B))

  (check-equal? (intersect ? ?) (rwild EAB))
  (check-equal? (intersect 'a ?) (rseq 'a EAB))
  (check-equal? (intersect 123 ?) (rseq 123 EAB))
  (check-equal? (intersect (cons ? 2) (cons 1 ?)) (rseq* SOP 1 2 EOS EAB))
  (check-equal? (intersect (cons 1 2) ?) (rseq* SOP 1 2 EOS EAB))
  (check-equal? (intersect 1 2) #f)
  (check-equal? (intersect (cons 1 2) (cons ? 2)) (rseq* SOP 1 2 EOS EAB))
  (check-equal? (intersect (cons 1 2) (cons 3 2)) #f)
  (check-equal? (intersect (cons 1 2) (cons 1 3)) #f)
  (check-equal? (intersect (vector 1 2) (vector 1 2)) (rseq* SOV 1 2 EOS EAB))
  (check-equal? (intersect (vector 1 2) (vector 1 2 3)) #f)

  (check-equal? (intersect (a 'a) (a 'b)) #f)
  (check-equal? (intersect (a 'a) (a 'a)) (rseq* struct:a 'a EOS EAB))
  (check-equal? (intersect (a 'a) (a ?)) (rseq* struct:a 'a EOS EAB))
  (check-equal? (intersect (a 'a) ?) (rseq* struct:a 'a EOS EAB))
  (check-equal? (intersect (b 'a) (b 'b)) #f)
  (check-equal? (intersect (b 'a) (b 'a)) (rseq* struct:b 'a EOS EAB))
  (check-equal? (intersect (b 'a) (b ?)) (rseq* struct:b 'a EOS EAB))
  (check-equal? (intersect (b 'a) ?) (rseq* struct:b 'a EOS EAB))

  (check-equal? (intersect (a 'a) (b 'a)) #f)

  (check-exn #px"Cannot match on hash tables at present"
	     (lambda ()
	       (intersect (hash 'a 1 'b ?) (hash 'a ? 'b 2))))
  ;; (check-equal? (intersect (hash 'a 1 'b ?) (hash 'a ? 'b 2)) (hash 'a 1 'b 2))
  ;; (check-equal? (intersect (hash 'a 1 'b ?) (hash 'a ?)) (void))
  ;; (check-equal? (intersect (hash 'a 1 'b ?) (hash 'a 1 'b ?)) (hash 'a 1 'b ?))
  ;; (check-equal? (intersect (hash 'a 1 'b ?) (hash 'a ? 'c ?)) (void))

  ;; (check-equal? (intersect (hash 'a 1 'b ?) (hash 'a 1 'b (list 2 ?)))
  ;; 		(hash 'a 1 'b (list 2 ?)))
  ;; (check-equal? (intersect (hash 'a 1 'b (list ? 3)) (hash 'a 1 'b (list 2 ?)))
  ;; 		(hash 'a 1 'b (list 2 3)))

  )

(module+ test
  (let ((abc (foldr matcher-union (matcher-empty)
		    (list (pattern->matcher 'A (list 'a ?))
			  (pattern->matcher 'B (list 'b ?))
			  (pattern->matcher 'C (list 'c ?)))))
	(bcd (foldr matcher-union (matcher-empty)
		    (list (pattern->matcher 'B (list 'b ?))
			  (pattern->matcher 'C (list 'c ?))
			  (pattern->matcher 'd (list 'd ?))))))
    (matcher-match-matcher abc (matcher-relabel bcd (lambda (old) (set #t))))))

(module+ test
  (check-equal? (compile-projection (list 'a 'b))
		(list SOP 'a SOP 'b '() EOS EOS EOS))
  (check-equal? (compile-projection (list 'a ?!))
		(list SOP 'a SOP ?! '() EOS EOS EOS))

  (check-equal? (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						(pattern->matcher 'B (list 'a 'b)))
				 (compile-projection (list 'a ?!)))
		(matcher-union (pattern->matcher #t (vector 'a))
			       (pattern->matcher #t (vector 'b))))

  (check-equal? (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						(pattern->matcher 'B (list 'a (vector 'b 'c 'd))))
				 (compile-projection (list 'a ?!)))
		(matcher-union (pattern->matcher #t (vector 'a))
			       (pattern->matcher #t (vector (vector 'b 'c 'd)))))

  (check-equal? (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						(pattern->matcher 'B (list 'a (vector 'b ? 'd))))
				 (compile-projection (list 'a ?!)))
		(matcher-union (pattern->matcher #t (vector 'a))
			       (pattern->matcher #t (vector (vector 'b ? 'd)))))

  (check-equal? (matcher->finite-set
		 (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						 (pattern->matcher 'B (list 'a 'b)))
				  (compile-projection (list 'a ?!))))
		(set '#(a) '#(b)))

  (check-equal? (matcher->finite-set
		 (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						 (pattern->matcher 'B (list 'a (vector 'b 'c 'd))))
				  (compile-projection (list 'a ?!))))
		(set '#(a) '#(#(b c d))))

  (check-equal? (matcher->finite-set
		 (matcher-project (matcher-union (pattern->matcher 'A (list 'a 'a))
						 (pattern->matcher 'B (list 'a (vector 'b ? 'd))))
				  (compile-projection (list 'a ?!))))
		#f)

  (check-equal? (matcher-project (matcher-union (pattern->matcher 'A (cons 1 2))
						(pattern->matcher 'B (cons 3 4)))
				 (compile-projection (cons ?! ?!)))
		(matcher-union (pattern->matcher #t (vector 1 2))
			       (pattern->matcher #t (vector 3 4))))

  (check-equal? (matcher->finite-set
		 (matcher-project (matcher-union (pattern->matcher 'A (cons 1 2))
						 (pattern->matcher 'B (cons 3 4)))
				  (compile-projection (cons ?! ?!))))
		(set '#(1 2) '#(3 4)))
  )