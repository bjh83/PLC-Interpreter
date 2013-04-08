;Brendan Higgins

(load "functionParser.scm")

;Returns a new environment
(define newEnviron
  (lambda () '((()())) )
  )

;Pushes a new environment frame on to the environment
(define push
  (lambda (environ)
	(cons '(()()) environ)
	)
  )

;Pops the top layer off the environment and returns it
(define head
  (lambda (environ)
	(if (null? environ)
	  (error "Environment is null")
	  (car environ)
	  )
	)
  )

;Returns the top layer identifier list of an environment
(define getVars
  (lambda (environ)
	(car (head environ))
	)
  )

;Returns the top layer store of an environment
(define getStore
  (lambda (environ)
	(car (cdr (head environ)))
	)
  )

;Pops the top layer of the environment and returns the resulting environment
(define tail
  (lambda (environ)
	(cond
	  ((null? environ) (error "Environment is null"))
	  (else (cdr environ))
	  )
	)
  )

;Pops the top layer of the environment and returns the resulting environment
(define pop tail)

;Returns whether a value is in a list
(define inList?
  (lambda (var l)
	(cond
	  ((null? l) #f)
	  ((eq? (car l) var) #t)
	  (else (inList? var (cdr l)))
	  )
	)
  )

;Returns whether a variable is in the top layer of an environment
(define inLayer?
  (lambda (var environ)
	(inList? var (getVars environ))
	)
  )

;Returns the index of a value in a list
(define getIndex
  (lambda (var l)
	(cond
	  ((null? l) (error "Variable not in list"))
	  ((eq? (car l) var) 0)
	  (else (+ 1 (getIndex var (cdr l))))
	  )
	)
  )

;Returns the value in a list corresponding to the specified index
(define getByIndex
  (lambda (index l)
	(if (= index 0)
	  (car l)
	  (getByIndex (- index 1) (cdr l))
	  )
	)
  )

;Declares a value in the top layer of an environment initializing it to null
(define declareVar
  (lambda (var environ)
	(cons (cons (cons var (getVars environ)) (cons (cons (box 'null) (getStore environ)) '())) (tail environ))
	)
  )

;Returns the value that is bound to a variable in the environment
(define lookup
  (lambda (var environ)
	(if (inLayer? var environ)
	  (unbox (getByIndex (getIndex var (getVars environ)) (getStore environ)))
	  (lookup var (tail environ))
	  )
	)
  )

;Binds a value to the most recent declaration of var
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

;determines whether val is a variable or a constant and will either look it up
;or just return it respectively.
(define getVal
  (lambda (val environ)
	(if (or (number? val) (eq? 'null val))
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
	  ((and (list? stmt) (eq? (car stmt) 'funcall)) (funcall-stmt stmt environ))
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

;takes an if statement, evaluates the appropriate condition expression, and continues interpreting the appropriate subexpression
;	This version does not take a break/continue continuation
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
	  ((eq? (car stmt) 'funcall) ((lambda (throw-away) environ)(funcall-stmt stmt environ)))
	  ((eq? (car stmt) 'break) (break 'break))
	  ((eq? (car stmt) 'continue) (break 'continue))
	  (else (basic-stmt stmt environ))
	  )
	)
  )

;Takes a parameter and a target value and assigns the value of var to parameter
(define declare-param
  (lambda (param var oldenv newenv)
	(cond
	  ((number? var) (assign param var (declareVar param newenv)))
	  ((list? var) (assign param (basic-stmt var oldenv) (declareVar param newenv)))
	  (else (assign param (lookup var oldenv) (declareVar param newenv)))
	  )
	)
  )

;Takes a list of parameters and a list of target values assigning the value of each target values to the parameters
(define declare-params
  (lambda (paramlist varlist oldenv newenv)
	(if (null? paramlist)
	  newenv
	  (declare-params (cdr paramlist) (cdr varlist) oldenv (declare-param (car paramlist) (car varlist) oldenv newenv))
	  )
	)
  )

;Looks up a function in the environment returning the body of the function
(define lookup-body
  (lambda (name environ)
	(car (cdr (lookup name environ)))
	)
  )

;Looks up a function in the environment returning the parameter list of the function
(define lookup-params
  (lambda (name environ)
	(car (lookup name environ))
	)
  )

;Takes a statement and an environment and executes the function represented 
;	in the statement and returns the return value of the function
(define funcall-stmt
  (lambda (stmt environ)
	(interpret-tree (lookup-body (car (cdr stmt)) environ) (declare-params (lookup-params (car (cdr stmt)) environ) (cdr (cdr stmt)) environ (push (pop environ))))
	)
  )

;Takes a statement in which a function is declared and creates a parameter list function body pair
;	for storing in the environment
(define funcify
  (lambda (stmt)
	(cons (car (cdr (cdr stmt))) (cons (car (cdr (cdr (cdr stmt)))) '()))
	)
  )

;stores a function in the enviroment or calls it if it is the main function
(define function-stmt
  (lambda (stmt environ return)
	(if (eq? (car (cdr stmt)) 'main)
	  (return (interpret-tree (car (cdr (cdr (cdr stmt)))) (push environ)))
	  (assign (car (cdr stmt)) (funcify stmt) (declareVar (car (cdr stmt)) environ))
	  )
	)
  )

;defines a new scope region does not take a break/continue continuation
(define begin-stmt
  (lambda (stmt environ return)
	(begin-stmt* stmt environ return (lambda () (error "not in loop")))
	)
  )

;defines a new scope region
(define begin-stmt*
  (lambda (stmt environ return break)
	(pop (interpret-inner-tree (cdr stmt) (push environ) return break))
	)
  )

;loops throug a set of statements to represent a while loop
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

;interprets a tree of statements inside a while loop or a new level of scope
(define interpret-inner-tree
  (lambda (tree environ return break)
	(cond
	  ((null? tree) environ)
	  (else (interpret-inner-tree (cdr tree) (full-stmt* (car tree) environ return break) return break))
	  )
	)
  )

;interprets a tree of statements
(define interpret-tree
  (lambda (tree environ)
	(call/cc
	  (lambda (return)
		(letrec ((loop
				   (lambda (tree environ)
					 (if (null? tree)
					   (return 'null)
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

