;; A meta-circular interpreter in Scheme
;; Adapted from http://paulgraham.com/rootsoflisp.html
;; This variant tests the let, cond and let* syntax.

(let* ((eq eqv?)
       (atom (lambda (x) (if (null? x) #t (if (symbol? x) #t #f))))
       (not (lambda (x) (if x #f #t)))
       (and (lambda (x y) (if x (if y #t #f) #f)))
       (cadr (lambda (x) (car (cdr x))))
       (caddr (lambda (x) (car (cdr (cdr x)))))
       (caar (lambda (x) (car (car x))))
       (caddar (lambda (x) (car (cdr (cdr (car x))))))
       (cadar (lambda (x) (car (cdr (car x)))))
       (assoc
        (recursive
         (lambda (assoc)
           (lambda (x y)
             (if (eq (caar y) x)
                 (cadar y)
                 (assoc x (cdr y)))))))
       (pair
        (recursive
         (lambda (pair)
           (lambda (x y)
             (if (and (null? x) (null? y))
                 '()
                 (if (and (not (atom x))
                          (not (atom y)))
                     (cons (list (car x) (car y))
                           (pair (cdr x) (cdr y)))))))))
       (append
        (recursive
         (lambda (append)
           (lambda (x y)
             (if (null? x)
                 y
                 (cons (car x) (append (cdr x) y)))))))
       (evcon
        (recursive
         (lambda (evcon)
           (lambda (eval)
             (lambda (c a)
               (if (eval (caar c) a)
                   (eval (cadar c) a)
                   ((evcon eval) (cdr c) a)))))))
       (evlis
        (recursive
         (lambda (evlis)
           (lambda (eval)
             (lambda (m a)
               (if (null? m)
                   '()
                   (cons (eval (car m) a)
                         ((evlis eval) (cdr m) a))))))))
       (eval
        (recursive
         (lambda (eval)
           (lambda (e a)
             (cond ((atom e)
                    (assoc e a))
                   ((atom (car e))
                    (cond ((eq (car e) 'quote) (cadr e))
                          ((eq (car e) 'atom) (atom (eval (cadr e) a)))
                          ((eq (car e) 'eq) (eq (eval (cadr e) a)
                                                (eval (caddr e) a)))
                          ((eq (car e) 'car) (car (eval (cadr e) a)))
                          ((eq (car e) 'cdr)
                           (cdr (eval (cadr e) a)))
                          ((eq (car e) 'cons)
                           (cons (eval (cadr e) a)
                                 (eval (caddr e) a)))
                          ((eq (car e) 'cond)
                           ((evcon eval) (cdr e) a))
                          ('t
                           (eval (cons (assoc (car e) a)
                                       (cdr e))
                                 a))))
                   ((eq (caar e) 'label)
                    (eval (cons (caddar e) (cdr e))
                          (cons (list (cadar e) (car e)) a)))
                   ((eq (caar e) 'lambda)
                    (eval (caddar e)
                          (append (pair (cadar e)
                                        ((evlis eval) (cdr e) a))
                                  a)))))))))
  (eval '((label firstatom
                 (lambda (x)
                   (cond ((atom x) x)
                         ('t (firstatom (car x))))))
          y)
        '((y ((a b) (c d))))))
