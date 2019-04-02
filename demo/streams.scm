;; A fancier program that computes the first 20 prime numbers.

((lambda (recursive)
   ((lambda (not divisible? head tail integers-from)
      ((lambda (take filter-stream)
         ((lambda (sieve)
            ((lambda (primes)
               (take 20 primes))
             ;; primes
             (sieve (integers-from 2))))
          ;; sieve
          (recursive
           (lambda (sieve)
             (lambda (s)
               (cons (head s) (lambda () (sieve (filter-stream (lambda (x) (not (divisible? (head s) x))) (tail s))))))))))
       ;; take
       (recursive
        (lambda (take)
          (lambda (n s)
            (if (= n 0)
                '()
                (cons (head s) (take (- n 1) (tail s)))))))
       ;; filter-stream
       (recursive
        (lambda (filter-stream)
          (lambda (p s)
            (if (p (head s))
                (cons (head s) (lambda () (filter-stream p (tail s))))
                (filter-stream p (tail s))))))
       ))
    ;; not
    (lambda (b) (if b #f #t))
    ;; divisible?
    (lambda (a b)
      (= 0 (modulo b a)))
    ;; head
    car
    ;; tail
    (lambda (l) ((cdr l)))
    ;; integers-from
    (recursive
     (lambda (integers-from)
       (lambda (n)
         (cons n (lambda () (integers-from (+ n 1)))))))))
 ;; recursive
 (lambda (fn)
   ((lambda (h) (h h))
    (lambda (g)
      (fn (lambda arglist
            (apply (g g) arglist)))))))
