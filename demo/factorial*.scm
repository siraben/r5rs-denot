;; Factorial but with the let* special form.
(let* ((fact (recursive
              (lambda (fact)
                (lambda (n)
                  (if (eqv? 0 n)
                      1
                      (* n (fact (- n 1)))))))))
  (fact 6))
