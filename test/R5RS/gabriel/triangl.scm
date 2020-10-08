;;; TRIANGL -- Board game benchmark.

(define *board*
  (vector 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1))

(define *sequence*
  (vector 0 0 0 0 0 0 0 0 0 0 0 0 0 0))

(define *a*
  (vector 1 2 4 3 5 6 1 3 6 2 5 4 11 12
          13 7 8 4 4 7 11 8 12 13 6 10
          15 9 14 13 13 14 15 9 10
          6 6))

(define *b*
  (vector 2 4 7 5 8 9 3 6 10 5 9 8
          12 13 14 8 9 5 2 4 7 5 8
          9 3 6 10 5 9 8 12 13 14
          8 9 5 5))

(define *c*
  (vector 4 7 11 8 12 13 6 10 15 9 14 13
          13 14 15 9 10 6 1 2 4 3 5 6 1
          3 6 2 5 4 11 12 13 7 8 4 4))

(define *answer* '())

(define (attempt i depth)
  @sensitivity:FA
  (cond ((= depth 14)
         (set! *answer*
               (cons (cdr (vector->list *sequence*)) *answer*))
         #t)
        ((and (= 1 (vector-ref *board* (vector-ref *a* i)))
              (= 1 (vector-ref *board* (vector-ref *b* i)))
              (= 0 (vector-ref *board* (vector-ref *c* i))))
         (vector-set! *board* (vector-ref *a* i) 0)
         (vector-set! *board* (vector-ref *b* i) 0)
         (vector-set! *board* (vector-ref *c* i) 1)
         (vector-set! *sequence* depth i)
         (do ((j 0 (+ j 1))
              (depth (+ depth 1)))
             ((or (= j 36) (attempt j depth)) #f))
         (vector-set! *board* (vector-ref *a* i) 1)
         (vector-set! *board* (vector-ref *b* i) 1)
         (vector-set! *board* (vector-ref *c* i) 0) #f)
        (else #f)))

(define (test i depth)
  @sensitivity:FA
  (set! *answer* '())
  (attempt i depth)
  (car *answer*))

(equal? (test 22 1) '(22 34 31 15 7 1 20 17 25 6 5 13 32))
