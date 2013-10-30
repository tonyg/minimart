#lang racket/base

(require "pattern.rkt")
(require rackunit)

(struct a (x) #:prefab)
(struct b (x) #:transparent)

(define (intersect-or-void a b) (intersect a b values void))

(check-equal? (intersect-or-void ? ?) ?)
(check-equal? (intersect-or-void 'a ?) 'a)
(check-equal? (intersect-or-void 123 ?) 123)
(check-equal? (intersect-or-void (cons ? 2) (cons 1 ?)) (cons 1 2))
(check-equal? (intersect-or-void (cons 1 2) ?) (cons 1 2))
(check-equal? (intersect-or-void 1 2) (void))
(check-equal? (intersect-or-void (cons 1 2) (cons ? 2)) (cons 1 2))
(check-equal? (intersect-or-void (cons 1 2) (cons 3 2)) (void))
(check-equal? (intersect-or-void (cons 1 2) (cons 1 3)) (void))
(check-equal? (intersect-or-void (vector 1 2) (vector 1 2)) (vector 1 2))
(check-equal? (intersect-or-void (vector 1 2) (vector 1 2 3)) (void))

(check-equal? (intersect-or-void (a 'a) (a 'b)) (void))
(check-equal? (intersect-or-void (a 'a) (a 'a)) (a 'a))
(check-equal? (intersect-or-void (a 'a) (a ?)) (a 'a))
(check-equal? (intersect-or-void (a 'a) ?) (a 'a))
(check-equal? (intersect-or-void (b 'a) (b 'b)) (void))
(check-equal? (intersect-or-void (b 'a) (b 'a)) (b 'a))
(check-equal? (intersect-or-void (b 'a) (b ?)) (b 'a))
(check-equal? (intersect-or-void (b 'a) ?) (b 'a))

(check-equal? (intersect-or-void (hash 'a 1 'b ?) (hash 'a ? 'b 2)) (hash 'a 1 'b 2))
(check-equal? (intersect-or-void (hash 'a 1 'b ?) (hash 'a ?)) (void))
(check-equal? (intersect-or-void (hash 'a 1 'b ?) (hash 'a 1 'b ?)) (hash 'a 1 'b ?))
(check-equal? (intersect-or-void (hash 'a 1 'b ?) (hash 'a ? 'c ?)) (void))

(check-equal? (intersect-or-void (hash 'a 1 'b ?) (hash 'a 1 'b (list 2 ?)))
	      (hash 'a 1 'b (list 2 ?)))
(check-equal? (intersect-or-void (hash 'a 1 'b (list ? 3)) (hash 'a 1 'b (list 2 ?)))
	      (hash 'a 1 'b (list 2 3)))
