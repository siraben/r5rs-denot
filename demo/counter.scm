;; Mutable state

((lambda (count)
   ((lambda (the-counter)
      (list (the-counter) (the-counter) (the-counter) (the-counter)))
    (count 0)))
 (lambda (initial)
   (lambda ()
     (set! initial (+ 1 initial))
     initial)))
