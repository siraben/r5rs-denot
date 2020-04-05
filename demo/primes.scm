;; A fancier program that computes the first 20 prime numbers.

(define (not x) (if x #f #t))
(define (divisible? a b) (= 0 (modulo b a)))
(define head car)
(define (tail l) ((cdr l)))
(define (take n s)
  (if (= n 0)
      '()
      (cons (head s) (take (- n 1) (tail s)))))
(define (integers-from n)
  (cons n (lambda () (integers-from (+ n 1)))))
(define (sieve s)
  (cons (head s)
        (lambda ()
          (sieve (filter-stream
                  (lambda (x)
                    (not (divisible? (head s) x))) (tail s))))))
(define (filter-stream p s)
  (if (p (head s))
      (cons (head s) (lambda () (filter-stream p (tail s))))
      (filter-stream p (tail s))))

(define primes (sieve (integers-from 2)))

(take 20 primes)
