#lang racket

(require "../chez-init.rkt")
(provide bintree-to-list bintree-add leaf-node interior-node parse-exp unparse-exp)


(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left-tree bintree?)
   (right-tree bintree?)))

; I've provide this one as a sample to you.
; It's used by the testcases though  so don't mess with it.
(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      [interior-node (value left right)
                (list value
                      (bintree-to-list left)
                      (bintree-to-list right))]
      [leaf-node (datum)
                 datum])))
                
; Here's the one you need to solve
(define bintree-add
  (lambda (bt num)
    (cases bintree bt
      [interior-node (value left right)
                     (interior-node value
                                    (bintree-add left num)
                                    (bintree-add right num))]
      [leaf-node (val)
                 (leaf-node (+ val num))])))

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  [lit-exp
   (data number?)]
  [lambda-exp
   (id (cond-list? symbol?))
   (body (cond-list? expression?))]
  [app-exp
   (rator expression?)
   (rand expression?)])

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(pair? datum)
       (cond
         [(eqv? (car datum) 'lambda)
          (lambda-exp (car (2nd  datum))
                      (parse-exp (3rd datum)))]
         [else (app-exp (parse-exp (1st datum))
                        (parse-exp (2nd datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

(define unparse-exp
  (lambda (exp)
    (nyi)))

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

(define cond-list?
  (lambda (cond)
    (let ([not-cond (lambda (x)
                      (not (cond x)))])
      (lambda (ls)
        (if (null? (filter not-cond ls)) #t
            #f)))))

;My code to edit

(define lite-recur-def
  (lambda (init sym-f true-f false-f if-f lambda-f let-f list-f colon-f id-f)
    (letrec ([rec (lambda (lc def)
                    (cond
                      [(null? lc) init]
                      [(equal? lc #t) (true-f)]
                      [(equal? lc #f) (false-f)]
                      [(symbol? lc) (sym-f lc def)]
                      [(number? lc) lc]
                      [(equal? (car lc) 'if) (if-f (rec (cadr lc) def)
                                                   (rec (caddr lc) def)
                                                   (rec (cadddr lc) def))]
                      [(equal? (car lc) 'lambda) (lambda-f (cadr lc)
                                                           (rec (cddr lc) (cons (cadr lc) def)))]
                      [(equal? (car lc) 'let) (let ([split (let-spliter (cadr lc))])
                                                (let-f (car split)
                                                       (rec (cadr split) def)
                                                       (rec (caddr lc) (cons (car split) def))))]
                      [(equal? (car lc) ':) (colon-f (cadr lc)
                                                     (caddr lc)
                                                     def)]
                      [(list? (car lc)) (list-f (rec (car lc) def)
                                                    (rec (cdr lc) def))]
                      [else (id-f (rec (car lc) def)
                                  (rec (cdr lc) def))]))])
      rec)))

(define let-spliter
    (lambda (vars)
      (let loop ([v vars]
                 [r '()]
                 [lc '()])
        (if (null? v) (list r lc)
            (loop (cdr v) (append r (list (caar v))) (append lc (list (cadar v))))))))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))
