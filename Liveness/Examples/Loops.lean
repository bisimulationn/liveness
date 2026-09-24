import Liveness.Optimisation.Correctness
import Liveness.Optimisation.Compact
import Liveness.Interp
import Liveness.Pretty

namespace Liveness.Examples

open Stmt Expr VarSet

def loopCarried : Stmt :=
  seq (assign "x" (const 0))
    (seq (assign "y" (const 5))
      («while» (sub (var "x") (const 10))
        (seq (assign "x" (add (var "x") (const 1)))
          (assign "y" (add (var "y") (const 1))))))

def loopCarriedObs : VarSet := ["x"]

def loopCarriedExpected : Stmt :=
  seq (assign "x" (const 0))
    (seq skip
      («while» (sub (var "x") (const 10))
        (seq (assign "x" (add (var "x") (const 1))) skip)))

def countdown : Stmt :=
  seq (assign "i" (const 0))
    (seq (assign "acc" (const 0))
      («while» (lt (var "i") (var "n"))
        (seq (assign "acc" (add (var "acc") (mul (var "i") (var "i"))))
          (seq (assign "i" (add (var "i") (const 1)))
            (assign "dbg" (var "acc"))))))

def countdownObs : VarSet := ["acc"]

def countdownExpected : Stmt :=
  seq (assign "i" (const 0))
    (seq (assign "acc" (const 0))
      («while» (lt (var "i") (var "n"))
        (seq (assign "acc" (add (var "acc") (mul (var "i") (var "i"))))
          (seq (assign "i" (add (var "i") (const 1))) skip))))

def nonterminating : Stmt :=
  «while» (const 1) (seq (assign "y" (add (var "y") (const 1))) (assign "z" (const 0)))

def nonterminatingObs : VarSet := ["x"]

def nonterminatingExpected : Stmt := «while» (const 1) (seq skip skip)

def loopDependency : Stmt :=
  seq (assign "n" (const 3))
    («while» (var "n")
      (seq (assign "t" (sub (var "n") (const 1)))
        (seq (assign "n" (var "t")) (assign "u" (const 7)))))

def loopDependencyObs : VarSet := ["n"]

def loopDependencyExpected : Stmt :=
  seq (assign "n" (const 3))
    («while» (var "n")
      (seq (assign "t" (sub (var "n") (const 1)))
        (seq (assign "n" (var "t")) skip)))

theorem loopCarried_fixed :
    Equiv (liveIn («while» (sub (var "x") (const 10))
      (seq (assign "x" (add (var "x") (const 1))) (assign "y" (add (var "y") (const 1))))) ["x"])
      ["x"] :=
  liveIn_while_equiv_of _ _ _ (by decide) (by decide)

theorem loopCarried_liveIn : Equiv (liveIn loopCarried loopCarriedObs) [] := by
  simp only [loopCarried, loopCarriedObs, liveIn_seq]
  exact (liveIn_equiv (liveIn_equiv loopCarried_fixed)).trans ⟨by decide, by decide⟩

theorem loopCarried_optimise : optimise loopCarried loopCarriedObs = loopCarriedExpected := by
  simp only [loopCarried, loopCarriedObs, optimise_seq, optimise_while, liveIn_seq,
    optimise_congr _ loopCarried_fixed, optimise_congr _ (liveIn_equiv loopCarried_fixed)]
  decide

theorem loopCarried_correct : ObsEquiv loopCarriedObs loopCarried loopCarriedExpected :=
  loopCarried_optimise ▸ dse_correct loopCarried loopCarriedObs

theorem countdown_fixed :
    Equiv (liveIn («while» (lt (var "i") (var "n"))
      (seq (assign "acc" (add (var "acc") (mul (var "i") (var "i"))))
        (seq (assign "i" (add (var "i") (const 1))) (assign "dbg" (var "acc"))))) ["acc"])
      ["acc", "i", "n"] :=
  liveIn_while_equiv_of _ _ _ (by decide) (by decide)

theorem countdown_liveIn : Equiv (liveIn countdown countdownObs) ["n"] := by
  simp only [countdown, countdownObs, liveIn_seq]
  exact (liveIn_equiv (liveIn_equiv countdown_fixed)).trans ⟨by decide, by decide⟩

theorem countdown_optimise : optimise countdown countdownObs = countdownExpected := by
  simp only [countdown, countdownObs, optimise_seq, optimise_while, liveIn_seq,
    optimise_congr _ countdown_fixed, optimise_congr _ (liveIn_equiv countdown_fixed)]
  decide

theorem countdown_correct : ObsEquiv countdownObs countdown countdownExpected :=
  countdown_optimise ▸ dse_correct countdown countdownObs

theorem nonterminating_fixed :
    Equiv (liveIn («while» (const 1)
      (seq (assign "y" (add (var "y") (const 1))) (assign "z" (const 0)))) ["x"]) ["x"] :=
  liveIn_while_equiv_of _ _ _ (by decide) (by decide)

theorem nonterminating_optimise :
    optimise nonterminating nonterminatingObs = nonterminatingExpected := by
  simp only [nonterminating, nonterminatingObs, optimise_while,
    optimise_congr _ nonterminating_fixed]
  decide

theorem loopDependency_fixed :
    Equiv (liveIn («while» (var "n")
      (seq (assign "t" (sub (var "n") (const 1)))
        (seq (assign "n" (var "t")) (assign "u" (const 7))))) ["n"]) ["n"] :=
  liveIn_while_equiv_of _ _ _ (by decide) (by decide)

theorem loopDependency_liveIn : Equiv (liveIn loopDependency loopDependencyObs) [] := by
  simp only [loopDependency, loopDependencyObs, liveIn_seq]
  exact (liveIn_equiv loopDependency_fixed).trans ⟨by decide, by decide⟩

theorem loopDependency_optimise :
    optimise loopDependency loopDependencyObs = loopDependencyExpected := by
  simp only [loopDependency, loopDependencyObs, optimise_seq, optimise_while, liveIn_seq,
    optimise_congr _ loopDependency_fixed]
  decide

theorem loopDependency_correct :
    ObsEquiv loopDependencyObs loopDependency loopDependencyExpected :=
  loopDependency_optimise ▸ dse_correct loopDependency loopDependencyObs

theorem while_const_one_no_bigStep (s : Stmt) {t : Stmt} {σ σ' : State} (h : BigStep t σ σ')
    (ht : t = «while» (const 1) s) : False := by
  induction h with
  | whileFalse he => cases ht; simp [eval] at he
  | whileTrue _ _ _ _ ihw => exact ihw ht
  | _ => cases ht

theorem nonterminating_diverges (σ : State) : Diverges (nonterminating, σ) :=
  Diverges.of_not_terminates fun ⟨_, h⟩ =>
    while_const_one_no_bigStep _ (BigStep.of_terminates h) rfl

theorem nonterminating_optimised_diverges (σ : State) :
    Diverges (optimise nonterminating nonterminatingObs, σ) :=
  (dse_preserves_divergence nonterminating nonterminatingObs σ).1 (nonterminating_diverges σ)

theorem nonterminating_compact :
    optimiseCompact nonterminating nonterminatingObs = «while» (const 1) skip := by
  unfold optimiseCompact
  rw [nonterminating_optimise]
  decide

theorem loopCarried_compact :
    optimiseCompact loopCarried loopCarriedObs =
      seq (assign "x" (const 0))
        («while» (sub (var "x") (const 10)) (assign "x" (add (var "x") (const 1)))) := by
  unfold optimiseCompact
  rw [loopCarried_optimise]
  decide

theorem nonterminatingExpected_diverges (σ : State) : Diverges (nonterminatingExpected, σ) :=
  nonterminating_optimise ▸ nonterminating_optimised_diverges σ

end Liveness.Examples
