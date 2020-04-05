;; A meta-circular interpreter in Scheme
;; Adapted from http://paulgraham.com/rootsoflisp.html

;; This variant tests define.  Because of the way we desugar define
;; into let and set!, mutual recursion is also achieved easily.  

(define eq eqv?)
(define atom (lambda (x) (if (null? x) #t (if (symbol? x) #t #f))))
(define not (lambda (x) (if x #f #t)))
(define and (lambda (x y) (if x (if y #t #f) #f)))
(define cadr (lambda (x) (car (cdr x))))
(define caddr (lambda (x) (car (cdr (cdr x)))))
(define caar (lambda (x) (car (car x))))
(define caddar (lambda (x) (car (cdr (cdr (car x))))))
(define cadar (lambda (x) (car (cdr (car x)))))

(define (assoc x y)
  (if (eq (caar y) x)
      (cadar y)
      (assoc x (cdr y))))

(define (pair x y)
  (if (and (null? x) (null? y))
      '()
      (if (and (not (atom x))
               (not (atom y)))
          (cons (list (car x) (car y))
                (pair (cdr x) (cdr y))))))

(define (append x y)
  (if (null? x)
      y
      (cons (car x) (append (cdr x) y))))

(define (evcon c a)
  (if (eval (caar c) a)
      (eval (cadar c) a)
      (evcon (cdr c) a)))

(define (evlis m a)
  (if (null? m)
      '()
      (cons (eval (car m) a)
            (evlis (cdr m) a))))

(define (eval e a)
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
                (evcon (cdr e) a))
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
                             (evlis (cdr e) a))
                       a)))))
(eval '((label firstatom
               (lambda (x)
                 (cond ((atom x) x)
                       ('t (firstatom (car x))))))
        y)
      '((y ((a b) (c d)))))
