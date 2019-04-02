# Translating R5RS Scheme Denotational Semantics into Haskell

Currently implements the entire definition of Scheme under Section 7.2
"Formal Semantics" of the [R5RS
specification](https://schemers.org/Documents/Standards/R5RS/r5rs.pdf).
Which includes everything from `lambda` (and its variadic forms), to
`if`, `set!` and `call-with-current-continuation`.

Ensure Cabal is installed and build this project by running `cabal
run`.  The REPL will boot up.  Type an expression and hit ENTER to
evaluate it.

## Turn Greek into Haskell!
![R5RS denotational semantics for evaluating lambdas](lambda-def.png)

```haskell
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

### Factorial and REPL Example
```scheme
Scheme> (((lambda (fn) ((lambda (h) (h h)) (lambda (g) (fn (lambda (x) ((g g) x)))))) (lambda (f) (lambda (n) (if (eqv? 0 n) 1 (* n (f (- n 1))))))) 6)
Done.

[720]
```


## Usage
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
The result is a triple (String, [E], S), consisting of a string, a
list of results, and the final store (up to the first empty cell).

