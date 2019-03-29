# Translating R5RS Scheme Denotational Semantics into Haskell

Currently implements the entire definition of Scheme under Section 7.2
"Formal Semantics" of the [R5RS
specification](https://schemers.org/Documents/Standards/R5RS/r5rs.pdf).
Which includes everything from `lambda` (and its variadic forms), to
`if`, `set!` and `call-with-current-continuation`.

A parser specified by the EBNF in the paper is not yet implemented.

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


### Factorial Example
As usual with Scheme, with such limited primitives we can create any
program imaginable, for instance, factorial:
```scheme
(((lambda (fn)
    ((lambda (h) (h h))
     (lambda (g)
       (fn (lambda (x)
             ((g g) x))))))
  (lambda (f)
    (lambda (n)
      (if (zero? n)
          1
          (* n (f (- n 1))))))) 6)
```

Translating into the `Expr` datatype (which will later be done
with a parser), we get

```haskell
factYComb =
  App
    (Lambda ["m"] []
      (App (App yComb
            [Lambda ["f"] []
             (Lambda ["n"] []
              (If (App (Id "eqv?") [Id "n", Const (Number 0)])
                  (Const (Number 1))
                  (App (Id "*")
                       [Id "n",
                       App (Id "f")
                       [App (Id "-") [Id "n", Const (Number 1)]]])))])
          [Id "m"]))
    [Const (Number 6)]
```

We can run this program in the standard environment and store, with a
free space of 50 cells, giving us _just_ enough free space.

```haskell
λ> evalStd factYComb
("Done.",[720],[(#<undefined>,False),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<procedure>,True),(#<unspecified>,True),(6,True),(#<unspecified>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(#<unspecified>,True),(#<procedure>,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(6,True),(5,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(5,True),(4,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(4,True),(3,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(3,True),(2,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(2,True),(1,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(1,True),(0,True),(#<procedure>,True),(#<unspecified>,True),(#<procedure>,True),(#<unspecified>,True),(0,True)])
```
