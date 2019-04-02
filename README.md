# From denotational semantics to a Scheme interpreter written in Haskell
![R5RS denotational semantics for evaluating lambdas](lambda-def.png)

The R5RS Scheme specification is a 50-page beauty, outlining the
syntax and semantics of Scheme in easy to understand prose, and
concludes with a denotational semantics.  The semantics looks a lot
like Haskell because in a sense it _is_ Haskell!  We can turn the
above image into a Haskell code fragment:

```haskell
-- Evaluate a lambda expression with an environment, continuation and
-- store.
eval (Lambda is gs e0) p k =
  \s ->
    send
      (Ef
         ( new s
         , \es k' ->
             if length es == length is
               then tievals
                      ((\p' -> evalc gs p' (eval e0 p' k')) . extends p is)
                      es
               else wrong "wrong number of arguments"))
      k
      (update (new s) (Em Unspecified) s)
```

Currently, the standard environment contains the following primitive procedures:
```text
+ * - / mod < > = >= <= cons car cdr list eqv? set-car! apply call-with-values call-with-current-continuation call/cc
```

And the following special forms:
```text
(if <expr> <expr> <expr>)
(if <expr> <expr>)
(set! <id> <expr>)
(lambda <id>* <expr>*)
(lambda <id> <expr>*)
(lambda (<id>* . <id>) <expr>*)
(<expr> <expr>*)
```

Ensure Cabal is installed and build this project by running `cabal
run`.  The REPL will boot up.  Type an expression and hit ENTER to
evaluate it.

### Factorial and REPL Example
```scheme
Scheme> (((lambda (fn) ((lambda (h) (h h)) (lambda (g) (fn (lambda (x) ((g g) x)))))) (lambda (f) (lambda (n) (if (eqv? 0 n) 1 (* n (f (- n 1))))))) 6)
720
Memory used: 47 cells
```
Alternatively, read it from a file called `factorial.scm`, then run
`cabal repl` and type `repf "factorial.scm"` into GHCi.
```text
*SchemeRepl> repf "factorial.scm" 
720
Memory used: 59 cells
```
## Scheme AST as a Haskell Datatype
The Scheme program:
```scheme
((lambda (x) (+ x x)) 10)
```
Can be written in the Haskell `Expr` datatype as:
```haskell
prog = App (Lambda ["x"] [] (App (Id "+") [Id "x", Id "x"])) [Const (Number 10)]
```
Which can be evaluated in a standard environment and infinite store by running.

```haskell
evalStd prog
```
The result is a triple `(String, [E], S)`, consisting of a string, a
list of results, and the final store (up to the first empty cell).

