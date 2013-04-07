;Brendan Higgins

(load "loopSimpleParser.scm")

(define newEnviron
  (lambda () '((()())) )
  )

(define push
  (lambda (environ)
	(cons '(()()) environ)
	)
  )

(define head
  (lambda (environ)
	(if (null? environ)
	  (error "Environment is null")
	  (car environ)
	  )
	)
  )

(define getVars
  (lambda (environ)
	(car (head environ))
	)
  )

(define getStore
  (lambda (environ)
	(car (cdr (head environ)))
	)
  )

(define tail
  (lambda (environ)
	(cond
	  ((null? environ) (error "Environment is null"))
	  (else (cdr environ))
	  )
	)
  )

(define pop tail)

(define inList?
  (lambda (var l)
	(cond
	  ((null? l) #f)
	  ((eq? (car l) var) #t)
	  (else (inList? var (cdr l)))
	  )
	)
  )

(define inLayer?
  (lambda (var environ)
	(inList? var (getVars environ))
	)
  )

(define getIndex
  (lambda (var l)
	(cond
	  ((null? l) (error "Variable not in list"))
	  ((eq? (car l) var) 0)
	  (else (+ 1 (getIndex var (cdr l))))
	  )
	)
  )

(define getByIndex
  (lambda (index l)
	(if (= index 0)
	  (car l)
	  (getByIndex (- index 1) (cdr l))
	  )
	)
  )

(define declareVar
  (lambda (var environ)
	(cons (cons (cons var (getVars environ)) (cons (cons (box 'null) (getStore environ)) '())) (tail environ))
	)
  )

(define lookup
  (lambda (var environ)
	(if (inLayer? var environ)
	  (unbox (getByIndex (getIndex var (getVars environ)) (getStore environ)))
	  (lookup var (tail environ))
	  )
	)
  )

(define assign
  (lambda (var value environ)
	(letrec
	  ((return
		 (lambda (func) environ)
		 )
	   (assign*
		 (lambda (var* value* environ*)
		   (if (inLayer? var* environ*)
			 (return (set-box! (getByIndex (getIndex var* (getVars environ*)) (getStore environ*)) value*))
			 (assign* var* value* (tail environ*))
			 )
		   )
		 )
	   )
	  (assign* var value environ)
	  )
	)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;!!!   OLD CODE   !!!;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;determines whether val is a variable or a constant and will either look it up
;or just return it respectively.
(define getVal
  (lambda (val environ)
	(if (number? val)
	  val
	  (lookup val environ)
	  )
	)
  )

;takes an operation and two values and computes the result of the operation
(define execute
  (lambda (op val1 val2)
	(cond
	  ((eq? op '*) (* val1 val2))
	  ((eq? op '/) (quotient val1 val2))
	  ((eq? op '+) (+ val1 val2))
	  ((eq? op '-) (- val1 val2))
	  ((eq? op '%) (remainder val1 val2))
	  ((eq? op '>) (> val1 val2))
	  ((eq? op '<) (< val1 val2))
	  ((eq? op '==) (= val1 val2))
	  ((eq? op '>=) (>= val1 val2))
	  ((eq? op '<=) (<= val1 val2))
	  ((eq? op '!=) (not (= val1 val2)))
	  (else (error "Undefined operator"))
	  )
	)
  )

;returns the value of a basic expression made of only operations and operands
(define basic-stmt
  (lambda (stmt environ)
	(cond
	  ((not (list? stmt)) (getVal stmt environ))
	  ((and (list? stmt) (eq? (car stmt) 'funcall)) (funcall stmt))
	  ((and (= (length stmt) 2) (list? (car (cdr stmt)))) (- (basic-stmt (car (cdr stmt)) environ)))
	  ((= (length stmt) 2) (- (getVal (car (cdr stmt)) environ)))
	  ((and (list? (car (cdr stmt))) (list? (car (cdr (cdr stmt))))) (execute (car stmt) (basic-stmt (car (cdr stmt)) environ) (basic-stmt (car (cdr (cdr stmt))) environ)))
	  ((list? (car (cdr stmt))) (execute (car stmt) (basic-stmt (car (cdr stmt)) environ) (getVal (car (cdr (cdr stmt))) environ)))
	  ((list? (car (cdr (cdr stmt)))) (execute (car stmt) (getVal (car (cdr stmt)) environ) (basic-stmt (car (cdr (cdr stmt))) environ)))
	  (else (execute (car stmt) (getVal (car (cdr stmt)) environ) (getVal (car (cdr (cdr stmt))) environ)))
	  )
	)
  )

;assigns the a value given in the stmt to the result of the rest of the stmt
(define assign-stmt
  (lambda (stmt environ)
	(if (list? (car (cdr (cdr stmt))))
	  (assign (car (cdr stmt)) (basic-stmt (car (cdr (cdr stmt))) environ) environ)
	  (assign (car (cdr stmt)) (getVal (car (cdr (cdr stmt))) environ) environ)
	  )
	)
  )

;takes a declairation expression, declairs the variable in the environment, and assigns it the result of the subexpression 
(define declare-stmt
  (lambda (stmt environ)
	(cond
	  ((null? (cdr (cdr stmt))) (declareVar (car (cdr stmt)) environ))
	  ((list? (car (cdr (cdr stmt)))) (assign (car (cdr stmt)) (basic-stmt (car (cdr (cdr stmt))) environ) (declareVar (car (cdr stmt)) environ)))
	  (else (assign (car (cdr stmt)) (getVal (car (cdr (cdr stmt))) environ) (declareVar (car (cdr stmt)) environ)))
	  )
	)
  )

;takes an if statement, evaluates the appropriate condition expression, and continues interpreting the appropriate subexpression
(define if-stmt
  (lambda (stmt environ return break)
	(cond 
	  ((basic-stmt (car (cdr stmt)) environ) (full-stmt* (car (cdr (cdr stmt))) environ return break))
	  ((null? (cdr (cdr (cdr stmt)))) environ)
	  (else (full-stmt* (car (cdr (cdr (cdr stmt)))) environ return break))
	  )
	)
  )

(define full-stmt
  (lambda (stmt environ return)
	(full-stmt* stmt environ return (lambda (throw-away) (error "not in loop")))
	)
  )

;takes an expression and determines what type of expression it is and calls the appropriate type-expression
(define full-stmt*
  (lambda (stmt environ return break)
	(cond
	  ((eq? (car stmt) '=) (assign-stmt stmt environ))
	  ((eq? (car stmt) 'return) (return (basic-stmt (car (cdr stmt)) environ)))
	  ((eq? (car stmt) 'if) (if-stmt stmt environ return break))
	  ((eq? (car stmt) 'var) (declare-stmt stmt environ))
	  ((eq? (car stmt) 'begin) (begin-stmt* stmt environ return break))
	  ((eq? (car stmt) 'while) (while-stmt stmt environ return))
	  ((eq? (car stmt) 'function) (function-stmt stmt environ return))
	  ((eq? (car stmt) 'funcall) (funcall-stmt stmt))
	  ((eq? (car stmt) 'break) (break 'break))
	  ((eq? (car stmt) 'continue) (break 'continue))
	  (else (basic-stmt stmt environ))
	  )
	)
  )

(define declare-param
  (lambda (param var oldenv newenv)
	(assign param (lookup var oldenv) (declareVar param newenv))
	)
  )

(define declare-params
  (lambda (paramlist varlist oldenv newenv)
	(if (null? paramlist)
	  newenv
	  (declare-params (cdr paramlist) (cdr varlist) oldenv (declare-param (car paramlist) (car varlist) oldenv newenv))
	  )
	)
  )

(define lookup-body
  (lambda (name environ)
	(car (cdr (lookup name)))
	)
  )

(define lookup-params
  (lambda (name environ)
	(car (lookup name))
	)
  )

(define funcall-stmt
  (lambda (stmt environ)
	(interpret-tree (lookup-body (car (cdr stmt))) (declare-params (lookup-params (car cdr stmt)) (cdr (cdr stmt)) environ (push (pop environ))))
	)
  )

(define funcify
  (lambda (stmt)
	(cons (car (cdr (cdr stmt))) (cons (car (cdr (cdr (cdr stmt)))) '()))
	)
  )

(define function-stmt
  (lambda (stmt environ return)
	(if (eq? (car (cdr stmt)) 'main)
	  (assign (car (cdr stmt)) (funcify stmt) (declareVar (car (cdr stmt) environ)))
	  (return (interpret-tree (cdr (cdr (cdr stmt))) environ))
	)
  )

(define begin-stmt
  (lambda (stmt environ return)
	(begin-stmt* stmt environ return (lambda () (error "not in loop")))
	)
  )

(define begin-stmt*
  (lambda (stmt environ return break)
	(pop (interpret-inner-tree (cdr stmt) (push environ) return break))
	)
  )

(define while-stmt
  (lambda (stmt environ return)
	(letrec ((iteration
			   (lambda (stmt environ return)
				 (call/cc
				   (lambda (exit)
					 (if (basic-stmt (car (cdr stmt)) environ)
					   (interpret-inner-tree (cdr (cdr stmt)) environ return exit)
					   (exit 'break)
					   )
					 )
				   )
				 )
			   )
			 )
	  (if (eq? (iteration stmt environ return) 'break)
		environ
		(while-stmt stmt environ return)
		)
	  )
	)
  )

(define interpret-inner-tree
  (lambda (tree environ return break)
	(cond
	  ((null? tree) environ)
	  (else (interpret-inner-tree (cdr tree) (full-stmt* (car tree) environ return break) return break))
	  )
	)
  )

(define interpret-tree
  (lambda (tree environ)
	(call/cc
	  (lambda (return)
		(letrec ((loop
				   (lambda (tree environ)
					 (if (null? tree)
					   (error "Program ended without a return")
					   (loop (cdr tree) (full-stmt (car tree) environ return))
					   )
					 )
				   )
				 )
		  (loop tree environ)
		  )
		)
	  )
	)
  )

;calls the parser and passes the parse tree and an environment list to the interpret tree loop (interpret-tree)
(define interpret
  (lambda (filename)
	(interpret-tree (parser filename) (newEnviron))
	)
  )

