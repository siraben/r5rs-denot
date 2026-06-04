(list
  (call/cc (lambda (k) (k 42) 0))
  (call-with-values (lambda () (values 1 2)) +)
  ((lambda xs (apply + xs)) 4 5))
