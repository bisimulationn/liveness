import Liveness
import Liveness.Examples.StraightLine
import Liveness.Examples.Branching
import Liveness.Examples.Loops

open Liveness Liveness.Examples

def zeroState : State := fun _ => 0

def initial : State := (((zeroState.update "c" 1).update "a" 4).update "b" 9).update "n" 5

def observe (L : VarSet) (σ : State) : List (String × Int) := L.map fun x => (x, σ x)

def sameObservation (L : VarSet) (a b : Outcome) : Bool :=
  match a, b with
  | .finished σ₁, .finished σ₂ => observe L σ₁ == observe L σ₂
  | .outOfFuel _, .outOfFuel _ => true
  | _, _ => false

def setEq (A B : VarSet) : Bool := decide (A ⊆ B ∧ B ⊆ A)

structure Case where
  name : String
  program : Stmt
  observed : VarSet
  expected : Stmt
  expectedLiveIn : VarSet

def cases : List Case :=
  [ { name := "straight-line elimination", program := straightLine, observed := straightLineObs,
      expected := straightLineExpected, expectedLiveIn := [] },
    { name := "expression dependencies", program := expressionDeps, observed := expressionDepsObs,
      expected := expressionDeps, expectedLiveIn := ["a"] },
    { name := "branch-sensitive liveness", program := branching, observed := branchingObs,
      expected := branchingExpected, expectedLiveIn := ["c"] },
    { name := "comparison guard", program := comparisonGuard, observed := comparisonGuardObs,
      expected := comparisonGuardExpected, expectedLiveIn := ["a", "b"] },
    { name := "squares under a comparison loop", program := countdown, observed := countdownObs,
      expected := countdownExpected, expectedLiveIn := ["n"] },
    { name := "loop-carried dependency", program := loopCarried, observed := loopCarriedObs,
      expected := loopCarriedExpected, expectedLiveIn := [] },
    { name := "loop body dependency", program := loopDependency, observed := loopDependencyObs,
      expected := loopDependencyExpected, expectedLiveIn := [] },
    { name := "nontermination preservation", program := nonterminating,
      observed := nonterminatingObs, expected := nonterminatingExpected,
      expectedLiveIn := ["x"] } ]

def fuel : Nat := 2000

def describeOutcome (L : VarSet) : Outcome → String
  | .finished σ => "finished with " ++ toString (observe L σ)
  | .outOfFuel _ => "fuel exhausted after " ++ toString fuel ++ " steps"

def runCase (c : Case) : IO Bool := do
  let (target, liveSet) := dse c.program c.observed
  let shapeOk := target == c.expected
  let liveOk := setEq liveSet c.expectedLiveIn
  let srcRun := run fuel c.program initial
  let tgtRun := run fuel target initial
  let semOk := sameObservation c.observed srcRun tgtRun
  IO.println s!"== {c.name}"
  IO.println s!"observed: {c.observed}"
  IO.println "source:"
  IO.println (c.program.pretty)
  IO.println "optimised:"
  IO.println (target.pretty)
  IO.println s!"live-in: {liveSet}"
  IO.println s!"source run: {describeOutcome c.observed srcRun}"
  IO.println s!"target run: {describeOutcome c.observed tgtRun}"
  IO.println s!"shape {if shapeOk then "ok" else "MISMATCH"}, live-in {if liveOk then "ok" else "MISMATCH"}, observation {if semOk then "ok" else "MISMATCH"}"
  IO.println ""
  pure (shapeOk && liveOk && semOk)

def main : IO UInt32 := do
  let results ← cases.mapM runCase
  let failures := results.filter (· == false) |>.length
  if failures == 0 then
    IO.println s!"all {results.length} cases passed"
    pure 0
  else
    IO.println s!"{failures} of {results.length} cases failed"
    pure 1
