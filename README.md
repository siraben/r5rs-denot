# Translating the R5RS Denotational Semantics into Haskell
## Turn Greek
![R5RS denotational semantics for evaluating lambdas](lambda-def.png)

## Into Haskell!
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
