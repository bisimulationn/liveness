import Liveness.Optimisation.Correctness
import Liveness.Pretty

namespace Liveness.Examples

open Stmt Expr

def branching : Stmt :=
  seq (assign "x" (const 10))
    (ite (var "c") (assign "x" (const 20)) (assign "y" (const 30)))

def branchingObs : VarSet := ["x"]

def branchingExpected : Stmt :=
  seq (assign "x" (const 10)) (ite (var "c") (assign "x" (const 20)) skip)

example : optimise branching branchingObs = branchingExpected := by decide

example : liveIn branching branchingObs = ["c"] := by decide

def branchingBothOverwrite : Stmt :=
  seq (assign "x" (const 10))
    (ite (var "c") (assign "x" (const 20)) (assign "x" (const 30)))

example : optimise branchingBothOverwrite ["x"] =
    seq skip (ite (var "c") (assign "x" (const 20)) (assign "x" (const 30))) := by decide

def comparisonGuard : Stmt :=
  seq (assign "t" (mul (var "a") (const 2)))
    (seq (assign "y" (const 1))
      (ite (lt (var "t") (var "b")) (assign "x" (eq (var "a") (const 4))) (assign "x" (const 0))))

def comparisonGuardObs : VarSet := ["x"]

def comparisonGuardExpected : Stmt :=
  seq (assign "t" (mul (var "a") (const 2)))
    (seq skip
      (ite (lt (var "t") (var "b")) (assign "x" (eq (var "a") (const 4))) (assign "x" (const 0))))

example : optimise comparisonGuard comparisonGuardObs = comparisonGuardExpected := by decide

example : liveIn comparisonGuard comparisonGuardObs = ["b", "a"] := by decide

theorem branching_correct : ObsEquiv branchingObs branching branchingExpected := by
  have h := dse_correct branching branchingObs
  rwa [show optimise branching branchingObs = branchingExpected by decide] at h

end Liveness.Examples
