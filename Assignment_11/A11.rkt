#lang racket

(require "../chez-init.rkt")
(provide bintree-to-list bintree-add leaf-node interior-node parse-exp unparse-exp)

;List of can be used to check for a list of things!!!!!!!
; (define list-of-number (list-of? number?))

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
   (vars (listof symbol?))
   (body (listof expression?))]
  [lambda-rest-exp
   (var symbol?)
   (body (listof expression?))]
  [app-exp
   (op expression?)
   (args (listof expression?))]
  [let-exp
   (defs (listof binding?))
   (bodies (listof expression?))]
  [let*-exp
   (nested-lets expression?)
   (bodies (listof expression?))]
  [end-exp]
  [letrec-exp
   (defs (listof binding?))
   (bodies (listof expression?))]
  [namedlet-exp
   (name symbol?)
   (defs (listof binding?))
   (bodies (listof expression?))])

(define binding?
  (lambda (val)
    (cond
      [(not (pair? val)) #f]
      [(not (symbol? (car val))) #f]
      [(not (expression? (cdr val))) #f]
      [else #t])))

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (exp)
    (cond
      [(symbol? exp) (var-exp exp)]
      [(number? exp) (lit-exp exp)]
      [(pair? exp)
       (cond
         [(eqv? (car exp) 'lambda)
          (if (list? (cadr exp)) (lambda-exp (2nd  exp)
                                             (parse-exps (cddr exp)))
              (lambda-rest-exp (2nd exp)
                              (parse-exps (cddr exp))))]
         [(eqv? (car exp) 'let)
          (if (symbol? (cadr exp)) (namedlet-exp (2nd exp)
                                                 (parse-lets (3rd exp))
                                                 (parse-exps (cdddr exp)))
              (let-exp (parse-lets (2nd exp))
                       (parse-exps (cddr exp))))]
         [(eqv? (car exp) 'let*) (let*-exp (let-star-parse (2nd exp)
                                                           (end-exp))
                                           (parse-exps (cddr exp)))]
         [(eqv? (car exp) 'letrec) (letrec-exp (parse-lets (2nd exp))
                                               (parse-exps (cddr exp)))]
         [else (app-exp (parse-exp (1st exp))
                        (parse-exps (cdr exp)))])]
      [else (error 'parse-exp "bad expression: ~s" exp)])))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (sym) sym]
      [lit-exp (val) val]
      [lambda-exp (vars bodies)
                  (append (list 'lambda
                        vars)
                        (unparse-exps bodies))]
      [lambda-rest-exp (var bodies)
                       (append (list 'lambda
                        var)
                        (unparse-exps bodies))]
      [app-exp (op args)
               (append (list (unparse-exp op))
                       (unparse-exps args))]
      [let-exp (vars bodies)
               (append (list 'let
                             (unparse-lets vars))
                       (unparse-exps bodies))]
      [let*-exp (lets bodies)
                (append (list 'let*
                              (unparse-let* lets))
                        (unparse-exps bodies))]
      [end-exp ()
               'error]
      [letrec-exp (vars bodies)
                  (append (list 'letrec
                                (unparse-lets vars))
                          (unparse-exps bodies))]
      [namedlet-exp (name vars bodies)
                    (append (list 'let
                                  name
                                  (unparse-lets vars))
                            (unparse-exps bodies))])))

(define parse-exps
  (lambda (ls)
    (let loop ([l ls]
               [r '()])
      (if (null? l) r
          (loop (cdr l) (append r (list (parse-exp (car l)))))))))

(define parse-lets
  (lambda (defs)
    (let loop ([d defs]
               [r '()])
      (if (null? d) r
          (loop (cdr d) (append r (list (cons (caar d) (parse-exp (cadar d))))))))))

(define let-star-parse
  (lambda (vars bodies)
    (let loop ([v vars])
      (if (= (length v) 1) (let-exp (parse-lets (list (car v)))
                                    (list bodies))
          (let-exp (parse-lets (list (car v)))
                   (list (loop (cdr v))))))))

(define unparse-exps
  (lambda (ls)
    (let loop ([l ls]
               [r '()])
      (if (null? l) r
          (loop (cdr l) (append r (list (unparse-exp (car l)))))))))

(define unparse-lets
  (lambda (bindings)
    (let loop ([b bindings]
               [r '()])
      (if (null? b) r
          (loop (cdr b) (append r (list (list (caar b)
                                        (unparse-exp (cdar b))))))))))

(define unparse-let*
  (lambda (lets)
    (if (equal? (car lets) 'end-exp) '()
        (append (list (list (caaadr lets) (unparse-exp (cdaadr lets)))) (unparse-let* (caaddr lets))))))
; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

;My code to edit

;; (define unparse-expression
;;   (lambda (exp)
;;     (cases expression exp
;;       [var-exp (id) id]
;;       [lambda-exp (id body)
;;                   (list 'lambda (list id)
;;                         (unparse-expression body))]
;;       [app-exp (proc arg)
;;                (list (unparse-expression proc)
;;                      (unparse-expression arg))]
;;       [if-exp (cond then else)
;;               (list 'if
;;                     (unparse-expression cond)
;;                     (unparse-expression then)
;;                     (unparse-expression else))]
;;       [num-exp (num)
;;                num])))

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

;Test cases to check
(define tester
  (lambda (ls)
    (printf "~s: ~s\n" ls (equal? ls (unparse-exp (parse-exp ls))))))
(tester '(lambda (x) x(+ x y)))
(tester '(lambda (x) (+)))
(tester '(lambda x (+ x y)))
(tester '(let ((a 1)
               (b 2))
           (+ a b)))
(tester '(let* ((a 1)
                (b (+ a 2)))
           (+ a b)))
(tester '(letrec ((a (lambda (x)
                       x))
                  (b 1))
           (a 1)))
(tester '(let loop ((l ls)
                    (r 1))
           (loop 1)))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))
