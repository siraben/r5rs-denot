(define cell (cons 1 (cons 2 '())))

(set-car! cell 9)
(set-cdr! cell (cons 8 '()))

cell
