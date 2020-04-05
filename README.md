# An interpreter for R5RS Scheme based on formal semantics
![R5RS denotational semantics for evaluating lambdas](lambda-def.png)

The R5RS Scheme specification is a 50-page beauty, outlining the
syntax and semantics of Scheme in easy to understand prose, and
concludes with a formal semantics.  The semantics looks a lot like
Haskell because in a sense it _is_ Haskell!  We can turn the above
image into a Haskell code fragment:

```haskell
-- Evaluate a lambda expression with an environment e0, continuation κ
-- and store σ.
eval (Lambda is gs e0) ρ κ =
  \σ ->
    send
      (Ef
         ( new σ
         , \εs κ' ->
             if length εs == length is
               then tievals
                      ((\ρ' -> evalc gs ρ' (eval e0 ρ' κ')) . extends ρ is)
                      εs
               else wrong "wrong number of arguments"))
      κ
      (update (new σ) (Em Unspecified) σ)
```

Currently, the standard environment contains the following primitive
procedures:

```text
+ * - / modulo < > = >= <= cons car cdr list eqv? boolean? symbol?
procedure? pair? number? set-car! set-cdr! null? apply
call-with-values values call-with-current-continuation call/cc
string? symbol->string string->symbol string-append number->string
recursive
```

And the following core special forms:

```text
(if <expr> <expr> <expr>)
(if <expr> <expr>)
(set! <id> <expr>)
(lambda <id>* <expr>*)
(lambda <id> <expr>*)
(lambda (<id>* . <id>) <expr>*)
(<expr> <expr>*)
```

The following derived forms have been implemented.  Currently they are
parsed and expanded in Haskell, but a hygienic macro system will take
their place.

```text
'<expr>
(begin <expr>*)
(cond (<expr> <expr>)*)
(let ((<id> <expr>)*) <expr>*)
(letrec ((<id> <expr>)) <expr>*)
(and <expr>*)
(or <expr>*)
```

Ensure Cabal is installed and build this project by running `cabal
run`.  The REPL will boot up.  Type an expression and hit ENTER to
evaluate it.

### Usage Examples
```scheme
Scheme> (letrec ((fact (lambda (n) (if (= n 0) 1 (* n (fact (- n 1))))))) (fact 6))
720
Memory used: 60 cells
```
Alternatively, read it from a file in the `demo` folder, using GHCi:
```text
-- Factorial
SchemeRepl> repf "demo/factorial.scm"
720
Memory used: 59 cells

-- Primes via streams
SchemeRepl> repf "demo/primes.scm"
(2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71)
Memory used: 6410 cells

-- Mutable state
SchemeRepl> repf "demo/counter.scm"
(1 2 3 4)
Memory used: 15 cells
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

## Performance notes
The performance has been greatly improved due to the use of the
`Data.IntMap` library to implement the store.  Thus, the Scheme
interpreter runs reasonably fast.

### Performance Statistics
```text
SchemeRepl> :set +s
SchemeRepl> repf "demo/primes.scm"
(2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71)
Memory used: 6410 cells
(0.09 secs, 40,075,816 bytes)
SchemeRepl> repf "demo/eval-lets.scm"
a
Memory used: 848 cells
(0.03 secs, 26,300,920 bytes)
SchemeRepl> repf "demo/counter.scm"
(1 2 3 4)
Memory used: 15 cells
(0.01 secs, 2,253,408 bytes)
```

## Feature Plans
- [ ] Escaping characters in strings
- [ ] quasiquote/unquote
- [ ] Hygienic macro expansion, according to [this
      paper](https://legacy.cs.indiana.edu/~dyb/pubs/LaSC-5-4-pp295-326.pdf).
- [ ] Vectors (using IntMap as representation).
- [ ] Rewrite `eval` from a store-passing, continuation-passing
      interpreter to a monadic style.
  - [ ] Inject the resulting monad into `IO`.
    - [ ] Implement ports, and user I/O.
      
