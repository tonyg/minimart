#lang racket/base
;; Gestalts: representations of (replicated) state.

(require racket/set)
(require racket/match)

(require "route.rkt")

(provide (struct-out gestalt)
	 drop-gestalt
	 lift-gestalt
	 simple-gestalt
	 gestalt-empty
	 gestalt-combine
	 gestalt-union
	 strip-gestalt-label
	 label-gestalt)

;; A Gestalt is a (gestalt (Listof (Vectorof (Pairof Matcher
;; Matcher)))), representing the total interests of a process or group
;; of processes. The outer list has a present entry for each active
;; metalevel, starting with metalevel 0 in the car. The vectors each
;; have an entry for each active observer level at their metalevel.
;; The innermost pairs have cars holding matchers representing active
;; subscriptions, and cdrs representing active advertisements.
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

(define (drop-gestalt g)
  (match-define (gestalt metalevels) g)
  (if (null? metalevels) g (gestalt (cdr metalevels))))

(define (lift-gestalt g)
  (gestalt (cons '#() (gestalt-metalevels g))))

(define (simple-gestalt subs advs level metalevel)
  (define leaf (cons subs advs))
  (define vec (make-vector (+ level 1) (cons #f #f)))
  (vector-set! vec level leaf)
  (let loop ((n metalevel) (acc (list vec)))
    (if (zero? n)
	(gestalt acc)
	(loop (- n 1) (cons '#() acc)))))

(define (gestalt-empty) (gestalt '()))

(define (gestalt-combine g1 g2 matcher-combiner)
  (define (zu sa1 sa2)
    (cons (matcher-combiner (car sa1) (car sa2))
	  (matcher-combiner (cdr sa1) (cdr sa2))))
  (define (yu ls1 ls2)
    (define vl1 (vector-length ls1))
    (define vl2 (vector-length ls2))
    (define one-bigger? (> vl1 vl2))
    (define maxlen (max vl1 vl2))
    (define minlen (min vl1 vl2))
    (define result (make-vector maxlen #f))
    (for ((i (in-range 0 minlen)))
      (vector-set! result i (zu (vector-ref ls1 i) (vector-ref ls2 i))))
    (for ((i (in-range minlen maxlen)))
      (vector-set! result i (vector-ref (if one-bigger? vl1 vl2) i)))
    result)
  (define (xu mls1 mls2)
    (match* (mls1 mls2)
      [('() mls) mls]
      [(mls '()) mls]
      [((cons m1 mls1) (cons m2 mls2)) (cons (yu m1 m2) (xu mls1 mls2))]))
  (gestalt (xu (gestalt-metalevels g1)
	       (gestalt-metalevels g2))))

(define (gestalt-union g1 g2) (gestalt-combine g1 g2 matcher-union))

(define (gestalt-matcher-transform g f)
  (define (zu sa) (cons (f (car sa)) (f (cdr sa))))
  (define (yu ls) (for/vector [(z (in-vector ls))] (zu z)))
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
		(gestalt (list (vector (cons 'a 'b)))))
  (check-equal? (simple-gestalt 'a 'b 2 2)
		(gestalt (list '#() '#() (vector (cons #f #f)
						 (cons #f #f)
						 (cons 'a 'b))))))
