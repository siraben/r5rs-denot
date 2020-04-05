(define (even? x) (cond
                   ((= x 0) #t)
                   ((= x 1) #f)
                   (odd? (- x 1))))
(define (odd? x) (cond
                  ((= x 0) #f)
                  ((= x 1) #t)
                  (even? (- x 1))))
(cons (odd? 13) (even? 14))
