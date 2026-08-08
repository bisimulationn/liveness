import Liveness.Optimisation.Correctness
import Liveness.Pretty

namespace Liveness.Examples

open Stmt Expr

def straightLine : Stmt :=
  seq (assign "x" (const 10)) (seq (assign "y" (const 20)) (assign "x" (const 30)))

def straightLineObs : VarSet := ["x"]

def straightLineExpected : Stmt :=
  seq skip (seq skip (assign "x" (const 30)))

example : optimise straightLine straightLineObs = straightLineExpected := by decide

example : liveIn straightLine straightLineObs = [] := by decide

def expressionDeps : Stmt :=
  seq (assign "t" (add (var "a") (const 1))) (assign "x" (add (var "t") (const 2)))

def expressionDepsObs : VarSet := ["x"]

example : optimise expressionDeps expressionDepsObs = expressionDeps := by decide

example : liveIn expressionDeps expressionDepsObs = ["a"] := by decide

def overwrittenChain : Stmt :=
  seq (assign "t" (const 1)) (seq (assign "x" (var "t")) (assign "x" (const 5)))

example : optimise overwrittenChain ["x"] = seq skip (seq skip (assign "x" (const 5))) := by decide

theorem straightLine_correct : ObsEquiv straightLineObs straightLine straightLineExpected := by
  have h := dse_correct straightLine straightLineObs
  rwa [show optimise straightLine straightLineObs = straightLineExpected by decide] at h

end Liveness.Examples
