;; I am a comment!

;; This program is valid core Scheme, and computes factorial of 6.
(((lambda (fn)
    ((lambda (h) (h h))
     (lambda (g)
       (fn (lambda arglist
             (apply (g g) arglist))))))
  (lambda (f)
    (lambda (n)
      (if (eqv? 0 n)
          1
          (* n (f (- n 1))))))) 6)
