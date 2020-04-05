;; We can fake mutual recursion by extracting all top-level
;; definitions into a let expression, bound to an undefined value.

(let ((undef (if #f #f)))
  (let ((even? undef) (odd? undef))
    (set! even? (lambda (x) (if (= x 0) #t (odd? (- x 1)))))
    (set! odd? (lambda (x) (if (= x 1) #t (even? (- x 1)))))
    (odd? 13)))
