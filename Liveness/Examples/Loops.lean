import Liveness.Optimisation.Correctness
import Liveness.Interp
import Liveness.Pretty

namespace Liveness.Examples

open Stmt Expr

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

end Liveness.Examples
