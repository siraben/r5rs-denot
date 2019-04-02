module SchemeTests where
import SchemeTypes
import SchemeEval

sId = Lambda ["x"] [] (Id "x")

sFst = Lambda ["x", "y"] [] (Id "x")

sSnd = Lambda ["x", "y"] [] (Id "y")

-- Curried first and second.
scFst = Lambda ["x"] [] (Lambda ["y"] [] (Id "x"))

scSnd = Lambda ["x"] [] (Lambda ["y"] [] (Id "y"))

idTest = App sId [Const (Number 3)]

fstTest = App sFst [Const (Number 3), Const (Number 5)]

sndTest = App sSnd [Const (Number 3), Const (Number 5)]

sFstTest = App (App scFst [Const (Number 3)]) [Const (Number 5)]

sSndTest = App (App scSnd [Const (Number 3)]) [Const (Number 5)]

addTest = App (Id "+") [Const (Number 3), Const (Number 5)]

addTest2 =
  App (Lambda ["x"] [] (App (Id "+") [Id "x", Id "x"])) [Const (Number 10)]

simpleList =
  App
    (Id "cons")
    [Const (Number 10), App (Id "cons") [Const (Number 20), Const Nil]]

carTest = App (Id "car") [simpleList]

cdrTest = App (Id "cdr") [simpleList]

factTest =
  App (Lambda ["x"] [] (App (Id "factorial") [Id "x"])) [Const (Number 6)]

ifTest :: Expr
ifTest =
  App
    (Lambda
       ["x"]
       []
       (If
          (App (Id "eqv?") [Id "x", Const (Number 0)])
          (Const (Number 10))
          (Const (Number 20))))
    [Const (Number 0)]

yComb =
  Lambda
    ["fn"]
    []
    (App
       (Lambda ["h"] [] (App (Id "h") [Id "h"]))
       [ Lambda
           ["g"]
           []
           (App
              (Id "fn")
              [Lambda ["x"] [] (App (App (Id "g") [Id "g"]) [Id "x"])])
       ])


{--
Factorial with the Y-combinator
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
--}
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
