;; A fancier program that computes the first 20 prime numbers.

((lambda (recursive)
   ((lambda (not)
      ((lambda (memo-proc divisible? head tail)
         ((lambda (integers-from take filter-stream)
            ((lambda (sieve)
               ((lambda (primes)
                  (take 20 primes))
                ;; primes
                (sieve (integers-from 2))))
             ;; sieve
             (recursive
              (lambda (sieve)
                (lambda (s)
                  (cons (head s) (memo-proc (lambda () (sieve (filter-stream (lambda (x) (not (divisible? (head s) x))) (tail s)))))))))))
          ;; integers-from
          (recursive
           (lambda (integers-from)
             (lambda (n)
               (cons n (memo-proc (lambda () (integers-from (+ n 1))))))))
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
                   (cons (head s) (memo-proc (lambda () (filter-stream p (tail s)))))
                   (filter-stream p (tail s))))))))
       ;; memo-proc
       (lambda (proc)
         ((lambda (already-run? result)
            (lambda ()
              (if (not already-run?)
                  ((lambda ()
                     (set! result (proc))
                     (set! already-run? #t)
                     result))
                  result)))
          #f
          '()))
       ;; divisible?
       (lambda (a b)
         (= 0 (modulo b a)))
       ;; head
       car
       ;; tail
       (lambda (l) ((cdr l)))
       ))
    ;; not
    (lambda (b) (if b #f #t))
    ))
 ;; recursive
 (lambda (fn)
   ((lambda (h) (h h))
    (lambda (g)
      (fn (lambda arglist
            (apply (g g) arglist)))))))
