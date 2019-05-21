;; Backtracking using call-with-current-continuation

;; In case testing on a real Scheme implementation.
;; (define recursive
;;   (lambda (fn)
;;     ((lambda (h) (h h))
;;      (lambda (g)
;;        (fn (lambda arglist
;;              (apply (g g) arglist)))))))

(let* ((current-continuation
        ;; Every procedure must have at least one argument, hence this.
        (lambda (_)
          (call-with-current-continuation
           (lambda (cc)
             (cc cc)))))
       (fail-stack '())
       (fail
        (lambda (_)
          (if (pair? fail-stack)
              (let ((back-track-point (car fail-stack)))
                (set! fail-stack (cdr fail-stack))
                (back-track-point back-track-point))

              ;; "error" out
              (set-car! 'exhausted-fail-stack '()))))
       (amb
        (lambda (choices)
          (let ((cc (current-continuation '())))
            (cond ((null? choices) (fail '()))
                  ((pair? choices) (let ((choice (car choices)))
                                     (set! choices (cdr choices))
                                     (set! fail-stack (cons cc fail-stack))
                                     choice))))))
       (assert
        (lambda (condition)
          (if condition
              #t
              (fail '()))))
       (output '())
       (display (lambda (thing)
                  (set! output (cons thing output))))
       (append (recursive
                (lambda (append)
                  (lambda (l s)
                    (if (null? l)
                        s
                        (cons (car l) (append (cdr l) s)))))))
       (reverse (recursive
                 (lambda (reverse)
                   (lambda (l)
                     (if (null? (cdr l))
                         (list (car l))
                         (append (reverse (cdr l)) (list (car l))))))))
       (a (amb '(1 2 3 4 5 6 7)))
       (b (amb '(1 2 3 4 5 6 7)))
       (c (amb '(1 2 3 4 5 6 7))))
  
  (assert (= (* c c) (+ (* a a) (* b b))))

  (display (list a b c))
  (assert (< b a))

  (display (list a b c))
  (reverse output))

;; Output is ((3 4 5) (4 3 5) (4 3 5))
