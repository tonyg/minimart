#lang racket/base

(require racket/set)
(require racket/match)
(require (only-in racket/port call-with-output-string))
(require (only-in racket/class object?))

(require rackunit)

(provide )

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

;; A Matcher is either
;; - #f, indicating no further matches possible
;; - a Set of Any, representing a successful match (if the end of the input has been reached)
;; - a Hashtable mapping (Sigma or wildcard) to Matcher
;; - a (wildcard-sequence Matcher)
;; If, in a hashtable matcher, a wild key is present, it is intended
;; to catch all and ONLY those keys not otherwise present in the
;; table.
(struct wildcard-sequence (matcher) #:transparent)

(define (rnull) #f)
(define (rempty? r) (not r))

(define (rvalue v) (set v))

(define (rseq e r)   (if (rempty? r) r (hash e r)))
(define (rwild r)    (rseq ? r))
(define (rwildseq r) (if (rempty? r) r (wildcard-sequence r)))

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

(module+ test
  (define (E . vs) (hash EOS (apply set vs)))
  (check-equal? (pattern->matcher 'A 123) (hash 123 (E 'A)))
  (check-equal? (pattern->matcher 'A (cons 1 2)) (hash SOP (hash 1 (hash 2 (hash EOS (E 'A))))))
  (check-equal? (pattern->matcher 'A (cons ? 2)) (hash SOP (hash ? (hash 2 (hash EOS (E 'A))))))
  (check-equal? (pattern->matcher 'A SOP) (hash struct:start-of-pair (hash EOS (E 'A))))
  (check-equal? (pattern->matcher 'A ?) (hash ? (E 'A)))
  )

(define (rlookup r key)
  (hash-ref r key (lambda () #f)))

(define (rupdate r key k)
  (if (rempty? k)
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
  (ror (rwild (rwildseq r))
       (rseq EOS r)))

(define ror
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

(define rand
  (let ()
    (define (walk re1 re2)
      (match* (re1 re2)
	[((wildcard-sequence r1) (wildcard-sequence r2)) (rwildseq (walk r1 r2))]
	[((wildcard-sequence r1) r2) (walk (expand-wildseq r1) r2)]
	[(r1 (wildcard-sequence r2)) (walk (expand-wildseq r2) r1)]
	[((? set? v1) (? set? v2)) (set-union v1 v2)]
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
		      [(#f k2) (walk-wild w1 key k2)]
		      [(k1 #f) (walk-wild w2 key k1)]
		      [(k1 k2) (walk k1 k2)])))]))
    (define (walk-wild w key k)
      (and w (cond
	      [(key-open? key) (walk (rwildseq w) k)]
	      [(key-close? key) (if (wildcard-sequence? w)
				    (walk (wildcard-sequence-matcher w) k)
				    #f)]
	      [else (walk w k)])))
    (lambda (re1 re2)
      (match* (re1 re2)
	[(#f r) #f]
	[(r #f) #f]
	[(r1 r2) (walk r1 r2)]))))

(define erase-path
  (let ()
    (define (cofinite-pattern)
      (error 'erase-path "Cofinite pattern required"))
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

(define (match-value r v)
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
	  (error 'match-value "Cannot match wildcard as a value")]
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
	  (when skipped? (error 'match-value "Cannot reflect on struct instance ~v" s))
	  (define fs (cdr (vector->list (struct->vector s))))
	  (match (rlookup r t)
	    [#f (walk-wild rest stack)]
	    [k (walk fs (cons rest stack) k)])]
	 [(cons v rest)
	  (match (rlookup r v)
	    [#f (walk-wild rest stack)]
	    [k (walk rest stack k)])])])))

(module+ test
  (define (pretty-print-matcher m [port (current-output-port)])
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
	       (define keystr (call-with-output-string (lambda (p) (display key p))))
	       (d keystr)
	       (walk (+ i 1 (string-length keystr)) k)
	       #t))]))
    (newline port)
    (walk 0 m)
    (newline port)
    (flush-output port)
    m)

  (define (check-matches matcher . tests)
    (let walk ((tests tests))
      (match tests
	['() (void)]
	[(list* message expectedstr rest)
	 (define actualset (match-value matcher message))
	 (printf "~v ==> ~v\n" message actualset)
	 (check-equal? actualset
		       (apply set (map (lambda (c) (string->symbol (string c)))
				       (string->list expectedstr))))
	 (walk rest)])))

  (void (pretty-print-matcher
	 (ror (pattern->matcher 'A (list (list ?) 'x))
	      (pattern->matcher 'B (list (list ?) 'y)))))

  (void (pretty-print-matcher
	 (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	      (pattern->matcher 'B (list (list 'c 'd) 'y)))))

  (void (pretty-print-matcher
	 (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	      (pattern->matcher 'B (list (list  ?  ?) 'y)))))

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	 (pattern->matcher 'B (list (list  ?  ?) 'x))))
   (list 'z 'x) ""
   (list (list 'z 'z) 'x) "B"
   (list (list 'z (list 'z)) 'x) "B"
   (list (list 'a 'b) 'x) "AB")

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	 (pattern->matcher 'B (list (list ?)     'y))))
   (list 'z 'y) ""
   (list (list 'z 'z) 'y) ""
   (list (list 'z 'z) 'x) ""
   (list (list 'a 'b) 'x) "A")

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	 (pattern->matcher 'B (list ? 'y))))
   (list 'z 'y) "B"
   (list (list 'z 'z) 'y) "B"
   (list (list 'a 'b) 'x) "A")

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list 'a 'b))
	 (pattern->matcher 'B (list 'c 'd))))
   (list 'a 'b) "A"
   (list 'c 'd) "B"
   (list 'a 'd) ""
   (list 'c 'b) "")

  (void (pretty-print-matcher (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
				   ;; Note: this is a largely nonsense matcher,
				   ;; since it expects no input at all
				   (rseq EOS (rvalue 'B)))))

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list (list 'a 'b) 'x))
	 (pattern->matcher 'B ?)))
   (list (list 'a 'b) 'x) "AB"
   'p "B"
   (list 'p) "B")

  (check-matches
   (pretty-print-matcher
    (ror (pattern->matcher 'A (list 'a ?))
	 (pattern->matcher 'B (list 'a (list 'b)))))

   (list 'a (list 'b)) "AB"
   (list 'a (list 'b 'b)) "A"
   (list 'a (list 'c 'c)) "A"
   (list 'a (list 'c)) "A"
   (list 'a (list (list))) "A"
   (list 'a (list)) "A"
   (list 'a 'x) "A")

  (check-matches
   (pretty-print-matcher
    (ror (ror (pattern->matcher 'A (list 'a ?))
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
    (ror (foldr ror (rnull) ps)
	 (pattern->matcher '+ (list 'Z (list ? '- ?)))))

  (void (pretty-print-matcher (bigdemo)))
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

  (check-matches (pretty-print-matcher (pattern->matcher 'A (list* 'a 'b ?)))
		 (list 'a 'b 'c 'd 'e 'f) "A"
		 (list 'b 'c 'd 'e 'f 'a) ""
		 3 "")

  (void (pretty-print-matcher (rand (pattern->matcher 'A (list 'a))
				    (pattern->matcher 'B (list 'b)))))

  (let ((r1 (ror (pattern->matcher 'A (list  ? 'b))
		 (pattern->matcher 'A (list  ? 'c))))
	(r2 (ror (pattern->matcher 'B (list 'a  ?))
		 (pattern->matcher 'B (list 'b  ?)))))
    (pretty-print-matcher (ror r1 r2))
    (pretty-print-matcher (ror r1 r1))
    (pretty-print-matcher (ror r2 r2))
    (pretty-print-matcher (rand r1 r2))
    (pretty-print-matcher (rand r1 r1))
    (pretty-print-matcher (rand r2 r2))
    (void))

  (void (pretty-print-matcher (rand (bigdemo) (pattern->matcher 'X (list 'm 'n)))))

  (check-matches
   (pretty-print-matcher (rand (bigdemo) (pattern->matcher 'X (list 'Z ?))))
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

  (let* ((r1 (pattern->matcher 'A (list  ? 'b)))
	 (r2 (pattern->matcher 'B (list 'a  ?)))
	 (r12 (ror r1 r2)))
    (printf "\n-=-=-=-=-=-=-=-=- erase1\n")
    (pretty-print-matcher r1)
    (pretty-print-matcher r2)
    (pretty-print-matcher r12)
    ;; TODO: these next two are not currently "minimal"
    (pretty-print-matcher (erase-path r1 r12))
    (pretty-print-matcher (erase-path r2 r12))
    (void))

  (let* ((r1 (ror (pattern->matcher 'A (list 'a ?))
		  (pattern->matcher 'A (list 'b ?))))
	 (r2 (pattern->matcher 'B (list 'b ?)))
	 (r12 (ror r1 r2)))
    (printf "\n-=-=-=-=-=-=-=-=- erase2\n")
    (pretty-print-matcher r12)
    (pretty-print-matcher (erase-path r1 r12))
    (pretty-print-matcher (erase-path r2 r12))
    (void))

  )

(module+ test
  (struct a (x) #:prefab)
  (struct b (x) #:transparent)

  (define (intersect a b)
    (rand (pattern->matcher 'A a)
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
