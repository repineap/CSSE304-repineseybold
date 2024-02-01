#lang racket

(require "../chez-init.rkt")
(require racket/trace)
(provide eval-one-exp reset-global-env)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

;; (define-datatype expression expression?  
;;   [var-exp        ; variable references
;;    (id symbol?)]
;;   [lit-exp        ; "Normal" data.  Did I leave out any types?
;;    (datum
;;     (lambda (x)
;;       (ormap 
;;        (lambda (pred) (pred x))
;;        (list number? vector? boolean? symbol? string? pair? null?))))]
;;   [app-exp        ; applications
;;    (rator expression?)
;;    (rands (list-of? expression?))]  
;;   )

(define-datatype expression expression?
  [var-exp
   (var symbol?)]
  [quote-exp
   (data quote-exp?)]
  [lit-exp
   (data lit-exp?)]
  [lambda-exp
   (vars (listof symbol?))
   (body (list-of? expression?))]
  [lambda-rest-exp
   (var symbol?)
   (body (list-of? expression?))]
  [app-exp
   (exps (listof expression?))]
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
   (bodies (listof expression?))]
  [if-exp
   (conditional expression?)
   (then expression?)
   (else expression?)]
  [when-exp
   (conditional expression?)
   (then expression?)]
  [set!-exp
   (id symbol?)
   (def expression?)]
  [or-exp
   (exps (listof expression?))]
  [and-exp
   (exps (listof expression?))]
  [cond-exp
   (conds (listof expression?))
   (bodies (listof expression?))]
  [begin-exp
    (bodies (listof expression?))]
  [define-exp
    (symbol symbol?)
    (value expression?)])
   

(define prim-proc?
  (lambda (exp)
    (member exp '(+ - * / add1 sub1 cons = zero? not < <= >= > car cdr list null? assq eq? equal? length list->vector list? pair? procedure? vector->list vector make-vector
                    vector-ref vector? number? symbol? vector-set! display newline))))

;;atom?

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [global-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals vector?)
   (env environment?)])

(define vector-of?
  (lambda (cond)
    (lambda (vec)
      (list-of? cond (vector->list vec)))))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (id (list-of? symbol?))
   (bodies (list-of? expression?))
   (env environment?)]
  [rest-closure
   (id symbol?)
   (bodies (list-of? expression?))
   (env environment?)]
  [cont-proc
   (k continuation?)])

;-------------------+
;                   |
; sec:CLOSURES      |
;                   |
;-------------------+

(define make-closure
  (lambda (id body env)
    (closure id body env)))
  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define binding?
  (lambda (val)
    (cond
      [(not (pair? val)) #f]
      [(not (symbol? (car val))) #f]
      [(not (expression? (cdr val))) #f]
      [else #t])))

(define (quote-exp? expr)
  (and (pair? expr)
       (= (length expr) 2)
       (eq? (car expr) 'quote)))

(define cr?
  (lambda (exp)
    (regexp-match? #rx"^c[ad]*r$" (symbol->string exp))))

(define lit-exp?
  (lambda (val)
    (cond
      [(number? val) #t]
      [(string? val) #t]
      [(equal? #t val) #t]
      [(equal? #f val) #t]
      [(equal? val (void)) #t]
      [(equal? (car val) (quote quote)) #t]
      [else #f])))

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (exp)
    (cond
      [(symbol? exp) (var-exp exp)]
      [(quote-exp? exp) (quote-exp exp)]
      [(lit-exp? exp) (lit-exp exp)]
      [(pair? exp)
       (cond
         [(eqv? (car exp) 'lambda)
          (let ([c (lambda-checker exp)]) (when c c))
          (if (list? (cadr exp)) (lambda-exp (2nd  exp)
                                             (parse-exps (cddr exp)))
              (lambda-rest-exp (2nd exp)
                               (parse-exps (cddr exp))))]
         [(eqv? (car exp) 'let)
          (if (symbol? (cadr exp)) (begin (let ([c (let-checker (cdr exp))]) (when c c))
                                          (namedlet-exp (2nd exp)
                                                        (parse-lets (3rd exp))
                                                        (parse-exps (cdddr exp))))
              (begin (let ([c (let-checker exp)]) (when c c))
                     (let-exp (parse-lets (2nd exp))
                              (parse-exps (cddr exp)))))]
         [(eqv? (car exp) 'let*)
          (let ([c (let-checker exp)]) (when c c))
          (let*-exp (let-star-parse (2nd exp)
                                    (parse-exps (cddr exp)))
                    (parse-exps (cddr exp)))]
         [(eqv? (car exp) 'letrec)
          (let ([c (let-checker exp)]) (when c c))
          (letrec-exp (parse-lets (2nd exp))
                      (parse-exps (cddr exp)))]
         [(eqv? (car exp) 'if)
          (let ([c (if-checker exp)]) (when c c))
          (if (null? (cdddr exp)) (when-exp (parse-exp (cadr exp))
                                                                 (parse-exp (caddr exp)))
                                   (if-exp (parse-exp (cadr exp))
                                           (parse-exp (caddr exp))
                                           (parse-exp (cadddr exp))))]
         [(eqv? (car exp) 'set!)
          (let ([c (set!-checker exp)]) (when c c))
          (let ([body (parse-exp (caddr exp))])
            (if (not (expression? body)) (error 'parse-exp "bad set! body: ~s" body)
                (set!-exp (cadr exp)
                          body)))]
         [(eqv? (car exp) 'begin)
          (begin-exp (parse-exps (cdr exp)))]
         [(eqv? (car exp) 'or)
          (or-exp (parse-exps (cdr exp)))]
         [(eqv? (car exp) 'and)
          (and-exp (parse-exps (cdr exp)))]
         [(eqv? (car exp) 'cond)
          (cond-exp (parse-exps (map car (cdr exp))) (parse-exps (map cadr (cdr exp))))]
         [(eqv? (car exp) 'define)
          (define-exp (cadr exp) (parse-exp (caddr exp)))]
         [else
          (let ([c (app-checker exp)]) (when c c))
          (app-exp (parse-exps exp))])]
      [else (error 'parse-exp "bad expression: ~s" exp)])))

(define split-let
  (lambda (bindings)
    (let loop ([vars '()]
               [vals '()]
               [init bindings])
      (if (null? init) (list vars vals)
          (loop (append vars (list (caar init))) (append vals (list (cdar init))) (cdr init))))))

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (var) var]
      [quote-exp (data) (cadr data)]
      [lit-exp (val) val]
      [lambda-exp (vars bodies)
                  (append (list 'lambda
                        vars)
                        (unparse-exps (vector->list bodies)))]
      [lambda-rest-exp (var bodies)
                       (append (list 'lambda
                        var)
                        (unparse-exps (vector->list bodies)))]
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
                            (unparse-exps bodies))]
      [if-exp (cond then else)
              (list 'if
                    (unparse-exp cond)
                    (unparse-exp then)
                    (unparse-exp else))]
      [when-exp (cond then)
                (list 'if
                      (unparse-exp cond)
                      (unparse-exp then))]
      [set!-exp (id def)
                (list 'set!
                      id
                      (unparse-exp def))])))

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
                                    bodies)
          (let-exp (parse-lets (list (car v)))
                   (list (loop (cdr v))))))))

(define lambda-checker
  (lambda (exp)
    (cond
      [(null? (cdr exp)) (error 'parse-exp "lambda missing vars: ~s" exp)]
      [(null? (cddr exp)) (error 'parse-exp "lambda missing body: ~s" exp)]
      [(and (not (symbol? (cadr exp))) (not ((listof symbol?) (cadr exp)))) (error 'parse-exp "non-symbol var: ~s" exp)]
      [else #f])))

(define app-checker
  (lambda (exp)
    (cond
      [(and (pair? exp) (not (list? exp))) (error 'parse-exp "app pair: ~s" exp)]
      [else #f])))

(define if-checker
  (lambda (exp)
    (cond
      [(null? (cdr exp)) (error 'parse-exp "if missing cond: ~s" exp)]
      [(null? (cddr exp)) (error 'parse-exp "if missing then: ~s" exp)])))

(define let-checker
  (lambda (exp)
    (cond
      [(null? (cdr exp)) (error 'parse-exp "let bindings null: ~s" exp)]
      [(null? (cddr exp)) (error 'parse-exp "let bodies missing: ~s" exp)]
      [(and (pair? (cadr exp)) (not (list? (cadr exp)))) (error 'parse-exp "let bindings bad: ~s" exp)]
      [(not ((listof valid-binding?) (cadr exp))) (error 'parse-exp "let bindings bad: ~s" exp)]
      [else #f])))

(define set!-checker
  (lambda (exp)
    (cond
      [(null? (cdr exp)) (error 'parse-exp "set! var missing: ~s" exp)]
      [(null? (cddr exp)) (error 'parse-exp "set! def missing: ~s" exp)]
      [else #f])))

(define valid-binding?
  (lambda (val)
    (and (list? val)
         (= 2 (length val))
         (symbol? (car val)))))

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

;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))
	    
(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [global-env-record ()
                         (apply-env (global-storage 'get) sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (vector-ref vals pos)
                                 (apply-env env sym)))])))

(define *prim-proc-names* '(test + - *  / add1 sub1 cons = zero? not < <= >= > car cdr list null? assq eq? equal? length list->vector list? pair? procedure? vector->list vector make-vector
                    vector-ref vector? number? symbol? vector-set! display newline map apply eqv? append quotient list-tail call/cc exit-list
                    caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr caaaar caaadr caadar caaddr cadaar
                    cadadr caddar cadddr cdaaar cdaadr cdadar cdaddr cddaar cddadr cdddar cddddr))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (list->vector (map prim-proc      
        *prim-proc-names*))
   (empty-env)))

(define global-storage
  (let ([env-state init-env])
    (lambda args
      (case (car args)
        [(add) (set! env-state (extend-env (list (cadr args)) (vector (caddr args)) env-state))]
        [(set)  (modify-env env-state (cadr args) (caddr args))]
        [(get) env-state]
        [(clear) (set! env-state init-env)]))))

;(trace global-storage)

(define modify-env
  (lambda (env sym newval)
    (cases environment env
      [empty-env-record ()
                        (error 'env "cannot set value of undefined var" sym)]
      [global-env-record ()
                         (global-storage 'set sym newval)]
      [extended-env-record (syms vals env)
                           (let ([pos (list-find-position sym syms)])
                             (if (number? pos)
                                 (vector-set! vals pos newval)
                                 (modify-env env sym newval)))])))

;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
  (lambda (exp)
    (cases expression exp
      [var-exp (id) exp]
      [quote-exp (val) exp]
      [lit-exp (val) exp]
      [lambda-exp (vars bodies) (lambda-exp vars
                                           (expand-syntaxes bodies))]
      [lambda-rest-exp (var bodies) (lambda-rest-exp var
                                                    (expand-syntaxes bodies))]
      [app-exp (exps) (app-exp (expand-syntaxes exps))]
      [let-exp (defs bodies)
               (let* ([split (split-let defs)]
                      [vars (car split)]
                      [vals (expand-syntaxes (cadr split))])
                 (app-exp (cons (lambda-exp vars
                                            (expand-syntaxes bodies))
                          vals)))]
      [let*-exp (nested bodies)
                (syntax-expand nested)]
      [letrec-exp (defs bodies) (let* ([split (split-lambdas defs)]
                                       [lams (car split)]
                                       [vals (cdr split)])
                                  (syntax-expand (let-exp (append (expand-syntaxes vals)
                                                                  (map (lambda (x) (cons (car x) (quote-exp ''undef))) lams))
                                                          (append (map (lambda (lam) (set!-exp (car lam) (syntax-expand (cdr lam)))) lams)
                                                                  (expand-syntaxes bodies)))))]
                                  
      [namedlet-exp (name defs bodies) (syntax-expand (letrec-exp (list (cons name (lambda-exp (map car defs)
                                                                                bodies)))
                                                                  (list (app-exp (cons (var-exp name) (map cdr defs))))))]
      [if-exp (conditional then else) (if-exp (syntax-expand conditional)
                                              (syntax-expand then)
                                              (syntax-expand else))]
      [when-exp (conditional then) (if-exp (syntax-expand conditional)
                                           (syntax-expand then)
                                           (lit-exp (void)))]
      [set!-exp (id def) (set!-exp id (syntax-expand def))]
      [or-exp (exps)
              (cond [(null? exps) (lit-exp #f)]
                    [(null? (cdr exps)) (syntax-expand (car exps))]
                    [else (syntax-expand (let-exp (list (cons 'or-part-dont-use-this-name (syntax-expand (car exps))))
                                                  (list (if-exp (var-exp 'or-part-dont-use-this-name)
                                                                (var-exp 'or-part-dont-use-this-name)
                                                                (syntax-expand (or-exp (cdr exps)))))))])]
      [and-exp (exps)
               (cond [(null? exps) (lit-exp #t)]
                     [(null? (cdr exps)) (syntax-expand (car exps))]
                     [else (if-exp (syntax-expand (car exps))
                                   (syntax-expand (and-exp (cdr exps)))
                                   (lit-exp #f))])]
      [begin-exp (exps) (app-exp (list (lambda-exp (list) (expand-syntaxes exps))))]
      [cond-exp (conds bodies) (cond
                                 [(null? conds) (lit-exp (void))]
                                 [(equal? 'else (cadar conds)) (syntax-expand (car bodies))]
                                 [else (if-exp (syntax-expand (car conds))
                                       (syntax-expand (car bodies))
                                       (syntax-expand (cond-exp (cdr conds) (cdr bodies))))])]
      [define-exp (sym value) (define-exp sym (syntax-expand value))]
      [else exp])))

(define expand-syntaxes
  (lambda (ls)
    (let loop ([r '()]
               [l ls])
      (if (null? l) r
          (loop (append r (list (syntax-expand (car l)))) (cdr l))))))

(define lambda-exp?
  (lambda (val)
    (if (expression? val)
        (cases expression val
          [lambda-exp (one two) #t]
          [lambda-rest-exp (one two) #t]
          [else #f])
        #f)))

(define split-lambdas
  (lambda (defs)
    (let loop ([lam '()]
               [val '()]
               [d defs])
      (if (null? d) (cons lam val)
          (if (lambda-exp? (cdar d)) (loop (append lam (list (car d))) val (cdr d))
              (loop lam (append val (list (car d))) (cdr d)))))))

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form (global-env-record) (init-k))))


(define reset-global-env
  (lambda ()
    (global-storage 'clear)))



(define-datatype continuation continuation?
  [init-k]
  [if-exp-k (env environment?) (then expression?) (else expression?) (k continuation?)]
  [proc-k (k continuation?)]
  [eval-rest-k (exps (listof expression?)) (env environment?) (k continuation?)]
  [cons-k (d scheme-value?) (k continuation?)]
  [last-k
   (k continuation?)]
  [modify-k
   (env environment?)
   (var symbol?)
   (k continuation?)]
  [global-add-k
   (sym symbol?)
   (k continuation?)]
  [map-rest-k
   (proc proc-val?)
   (args list?)
   (k continuation?)]
  [call/cc-k
   (k continuation?)])


(define apply-k
  (lambda (k v)
    (cases continuation k
      [init-k () v]
      [if-exp-k (env then else k) (if (equal? v #f)
                                        (eval-exp else env k)
                                        (eval-exp then env k))]
      [proc-k (k)
              (apply-proc (car v) (cdr v) k)]
      [eval-rest-k (exps env k)
                   (eval-exps exps env (cons-k v k))]
      [cons-k (d k)
              (apply-k k (cons d v))]
      [last-k (k)
              (apply-k k (last v))]
      [modify-k (env var k)
                (apply-k k (modify-env env var v))]
      [global-add-k (sym k)
                    (apply-k k (global-storage 'add sym v))]
      [map-rest-k (proc args k)
                  (map-proc proc args (cons-k v k))]
      [call/cc-k (rec)
                 (cases proc-val v
                   [closure (vars bodies env)
                            (eval-exps bodies
                                       (extend-env vars
                                                   (vector (cont-proc k))
                                                   env)
                                       k)]
                   [else 'error])])))

; eval-exp is the main component of the interpreter
(define eval-exp
  (lambda (exp env k)
    (cases expression exp
      ;;Literals are evaluated as their values
      [lit-exp (datum)(apply-k k datum)]
      ;;Quote expressions shed their quote
      [quote-exp (data) (apply-k k (cadr data))]
      ;;Variables such as x or + use the environment to apply their values
      [var-exp (id)
               (apply-k k (apply-env env id))]
      ;;If expressions evalute the conditions, if it is false it returns the value of the else, if it is true it returns the value of the then both evaluated
      [if-exp (cond then else)
               (eval-exp cond env (if-exp-k env then else k))]
      ;;Apps determine the value of the operator from the environment, then evaluate all the expressions and apply the proc to that
      [app-exp (exps)
               (eval-exps exps env (proc-k k))]
      ;;Lambda exps create closures with the vars, bodies, and the current environment
      [lambda-exp (vars bodies)
                  (apply-k k (closure vars bodies env))]
      ;;Same with rest exps
      [lambda-rest-exp (var bodies)
                       (apply-k k (rest-closure var bodies env))]
      [set!-exp (id def)
                (eval-exp def env (modify-k env id k))]
      [define-exp (sym value) (eval-exp value env (global-add-k sym k))]

      ;;^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ALL ABOVE in CPS ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of expressions, putting results into a list
(define eval-exps
  (lambda (exps env k)
    (if (null? exps)
        (apply-k k '())
        (eval-exp (car exps) env (eval-rest-k (cdr exps) env k)))))

;; (define eval-exps
;;   (lambda (rands env)
;;     (let loop ([r '()]
;;                [exps rands])
;;       (if (null? exps)
;;           r
;;           (loop (append r (list (eval-exp (car exps) env))) (cdr exps))))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
      ;;If primitive, simply applies the primitive
      [prim-proc (op) (apply-prim-proc op args k)]
      ;;If it is a closer, looks at the bodies and evaluates all of them in the context of the expanded environment based on the passed args pairing them with the vars in the closure and the env
      [closure (vars bodies env)
               (eval-exps bodies (extend-env vars (list->vector args) env) (last-k k))]
      [rest-closure (var bodies env)
                    (eval-exps bodies (extend-env (list var) (vector args) env) (last-k k))]
      [cont-proc (cont)
                 (apply-k cont (car args))]
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

;(trace apply-k)
;(trace eval-exp)
;(trace apply-proc)

;;Does caddr, caadr, etc. by looping
(define apply-cr
  (lambda (cr ls)
    (if (= (length cr) 1) ls
        (if (equal? (car cr) #\a) (apply-cr (cdr cr) (car ls))
            (apply-cr (cdr cr) (cdr ls))))))



(define base-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (list->vector (map prim-proc      
        *prim-proc-names*))
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args k)
    (case prim-proc
      [(+) (apply-k k (apply + args))]
      [(-) (apply-k k (apply - args))]
      [(*) (apply-k k (apply * args))]
      [(/) (apply-k k (apply / args))]
      [(add1) (apply-k k (+ (1st args) 1))]
      [(sub1) (apply-k k (- (1st args) 1))]
      [(cons) (apply-k k (cons (1st args) (2nd args)))]
      [(=) (apply-k k (= (1st args) (2nd args)))]
      [(zero?) (apply-k k (zero? (1st args)))]
      [(not) (apply-k k (not (1st args)))]
      [(<) (apply-k k (< (1st args) (2nd args)))]
      [(<=) (apply-k k (<= (1st args) (2nd args)))]
      [(>=) (apply-k k (>= (1st args) (2nd args)))]
      [(>) (apply-k k (> (1st args) (2nd args)))]
      [(car) (apply-k k (car (1st args)))]
      [(cdr) (apply-k k (cdr (1st args)))]
      [(list) (apply-k k args)]
      [(null?) (apply-k k (null? (1st args)))]
      [(assq) (apply-k k (assq (1st args) (2nd args)))]
      [(eq?) (apply-k k (eq? (1st args) (2nd args)))]
      [(equal?) (apply-k k (equal? (1st args) (2nd args)))]
      ;;[(atom?) (atom? (1st args))]
      [(length) (apply-k k (length (1st args)))]
      [(list->vector) (apply-k k (list->vector (1st args)))]
      [(list?) (apply-k k (list? (1st args)))]
      [(pair?) (apply-k k (pair? (1st args)))]
      [(procedure?) (apply-k k (proc-val? (1st args)))]
      [(vector->list) (apply-k k (vector->list (1st args)))]
      [(vector) (apply-k k (list->vector args))]
      [(make-vector) (apply-k k (make-vector (1st args)))]
      [(vector-ref) (apply-k k (vector-ref (1st args) (2nd args)))]
      [(vector?) (apply-k k (vector? (1st args)))]
      [(number?) (apply-k k (number? (1st args)))]
      [(symbol?) (apply-k k (symbol? (1st args)))]
      [(vector-set!) (apply-k k (vector-set! (1st args) (2nd args) (3rd args)))]
      [(display) (apply-k k (display (1st args)))]
      [(newline) (apply-k k (newline))]
      [(map) (map-proc (car args) (cdr args) k)]
      [(apply) (apply-proc (car args) (cadr args) k)]
      [(eqv?) (apply-k k (eqv? (1st args) (2nd args)))]
      [(append) (apply-k k (apply append args))]
      [(quotient) (apply-k k (quotient (1st args) (2nd args)))]
      [(list-tail) (apply-k k (list-tail (1st args) (2nd args)))]
      [(call/cc) (apply-proc (car args) (list (cont-proc k)) k)]
      [(exit-list) args]
      [else (if (cr? prim-proc) (apply-cr (cdr (reverse (string->list (symbol->string prim-proc)))) (1st args))
                (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc))])))

(define map-proc
  (lambda (proc args k)
    (if (null? (car args))
        (apply-k k '())
        (apply-proc proc (map car args) (map-rest-k proc (map cdr args) k)))))

;(trace map-proc)

;;(trace apply-prim-proc)

(define reverse
  (lambda (lst)
    (let loop ([lst lst] [lst-reversed '()])
      (if (empty? lst)
          lst-reversed
          (loop (rest lst) (cons (first lst) lst-reversed))))))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))


;; (app-exp
;;  (lambda-exp (x)
;;              ((app-exp (var-exp +)
;;                        ((var-exp x) (lit-exp 1)))
;;               (app-exp (var-exp +) ((var-exp x) (lit-exp 1)))))
;;  ((lit-exp 1)))


(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))