#lang racket/base

(require racket/match)
(require (only-in racket/class object?))

(provide ?
	 wildcard?
	 specialization?
	 ground?
	 intersect)

(struct exn:unification-failure ())
(define unification-failure (exn:unification-failure))
(define (fail) (raise unification-failure))

(struct wildcard ()
	#:transparent
	#:property prop:custom-write
	(lambda (v port mode)
	  (display "?" port)))

(define ? (wildcard))

;; Any -> Boolean
;; Racket objects are structures, so we reject them explicitly for
;; now, leaving them opaque to unification.
(define (non-object-struct? x)
  (and (struct? x)
       (not (object? x))))

;; True iff a is a specialization (or instance) of b.
(define (specialization? a b)
  (let walk ((a a) (b b))
    (cond
     [(wildcard? b) #t]
     [(wildcard? a) #f]
     [(and (pair? a) (pair? b))
      (and (walk (car a) (car b)) (walk (cdr a) (cdr b)))]
     [(and (vector? a) (vector? b) (= (vector-length a) (vector-length b)))
      (for/and ([aa a] [bb b]) (walk aa bb))]
     [(and (non-object-struct? a) (non-object-struct? b))
      (walk (struct->vector a #f) (struct->vector b #f))]
     [else (equal? a b)])))

;; Any -> Boolean
;; True iff the term is completely ground, that is has no variables or
;; canonical-variables in it.
(define (ground? x)
  (let walk ((x x))
    (cond
     [(wildcard? x) #f]
     [(pair? x) (and (walk (car x)) (walk (cdr x)))]
     [(vector? x) (andmap walk (vector->list x))]
     [(non-object-struct? x) (walk (struct->vector x #f))]
     [else #t])))

;; Vector StructType -> Struct
(define (vector->struct v t)
  (apply (struct-type-make-constructor t) (cdr (vector->list v))))

;; Any Any -> Any
(define (unify a b)
  (cond
   [(wildcard? a) b]
   [(wildcard? b) a]
   [(and (pair? a) (pair? b))
    (cons (unify (car a) (car b)) (unify (cdr a) (cdr b)))]
   [(and (vector? a) (vector? b))
    (unless (= (vector-length a) (vector-length b)) (fail))
    (for/vector ((va (in-vector a)) (vb (in-vector b))) (unify va vb))]
   [(and (non-object-struct? a) (non-object-struct? b))
    (define-values (ta ta-skipped?) (struct-info a))
    (define-values (tb tb-skipped?) (struct-info b))
    (unless (eq? ta tb) (fail))
    (when ta-skipped? (fail))
    (when tb-skipped? (fail))
    (vector->struct (unify (struct->vector a) (struct->vector b)) ta)]
   [(equal? a b)
    a]
   [else (fail)]))

;; Any Any (Any -> X) (-> X) -> X
(define (intersect a b ks kf)
  (define-values (ok? result)
    (with-handlers ([exn:unification-failure? (lambda (e) (values #f (void)))])
      (values #t (unify a b))))
  (if ok?
      (ks result)
      (kf)))
