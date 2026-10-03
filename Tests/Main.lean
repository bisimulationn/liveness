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

structure Rng where
  state : UInt64

def Rng.next (g : Rng) : Rng × Int :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  let v : Int := ((s >>> 33).toNat % 17 : Nat)
  (⟨s⟩, v - 8)

def randomState (g : Rng) : List String → Rng × State
  | [] => (g, zeroState)
  | x :: xs =>
    let (g, σ) := randomState g xs
    let (g, v) := g.next
    (g, σ.update x v)

def randomStates (g : Rng) (vars : List String) : Nat → Rng × List State
  | 0 => (g, [])
  | n + 1 =>
    let (g, σ) := randomState g vars
    let (g, rest) := randomStates g vars n
    (g, σ :: rest)

def samples : Nat := 25

def agreeOnSamples (L : VarSet) (source target compacted : Stmt) (states : List State) : Bool :=
  states.all fun σ =>
    let srcRun := run fuel source σ
    sameObservation L srcRun (run fuel target σ) && sameObservation L srcRun (run fuel compacted σ)

def describeOutcome (L : VarSet) : Outcome → String
  | .finished σ => "finished with " ++ toString (observe L σ)
  | .outOfFuel _ => "fuel exhausted after " ++ toString fuel ++ " steps"

def runCase (seed : UInt64) (c : Case) : IO Bool := do
  let (target, liveSet) := dse c.program c.observed
  let shapeOk := target == c.expected
  let liveOk := setEq liveSet c.expectedLiveIn
  let srcRun := run fuel c.program initial
  let tgtRun := run fuel target initial
  let semOk := sameObservation c.observed srcRun tgtRun
  let compacted := compact target
  let cmpRun := run fuel compacted initial
  let cmpOk := sameObservation c.observed srcRun cmpRun && compacted.size ≤ target.size
  let (_, states) := randomStates ⟨seed⟩ (c.program.vars ∪ c.observed) samples
  let randomOk := agreeOnSamples c.observed c.program target compacted states
  IO.println s!"== {c.name}"
  IO.println s!"observed: {c.observed}"
  IO.println "source:"
  IO.println (c.program.pretty)
  IO.println "optimised:"
  IO.println (target.pretty)
  IO.println "compacted:"
  IO.println (compacted.pretty)
  IO.println s!"live-in: {liveSet}"
  IO.println s!"source run: {describeOutcome c.observed srcRun}"
  IO.println s!"target run: {describeOutcome c.observed tgtRun}"
  IO.println s!"shape {if shapeOk then "ok" else "MISMATCH"}, live-in {if liveOk then "ok" else "MISMATCH"}, observation {if semOk then "ok" else "MISMATCH"}, compaction {if cmpOk then "ok" else "MISMATCH"}, {samples} random states {if randomOk then "ok" else "MISMATCH"}"
  IO.println ""
  pure (shapeOk && liveOk && semOk && cmpOk && randomOk)

def main (args : List String) : IO UInt32 := do
  let seed : UInt64 := match args with
    | s :: _ => s.toNat?.map (·.toUInt64) |>.getD 20260808
    | [] => 20260808
  IO.println s!"seed {seed}"
  let results ← cases.mapM (runCase seed)
  let failures := results.filter (· == false) |>.length
  if failures == 0 then
    IO.println s!"all {results.length} cases passed"
    pure 0
  else
    IO.println s!"{failures} of {results.length} cases failed"
    pure 1
