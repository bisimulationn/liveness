import Liveness.Observations

namespace Liveness

def freeVars : Expr → VarSet
  | .const _ => []
  | .var x => [x]
  | .add e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .sub e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .mul e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .lt e₁ e₂ => freeVars e₁ ∪ freeVars e₂
  | .eq e₁ e₂ => freeVars e₁ ∪ freeVars e₂

theorem eval_agree {e : Expr} {σ₁ σ₂ : State} (h : Agree (freeVars e) σ₁ σ₂) :
    eval σ₁ e = eval σ₂ e := by
  induction e with
  | const n => rfl
  | var x => exact h x (List.mem_singleton.2 rfl)
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ h.union_left, ih₂ h.union_right]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ h.union_left, ih₂ h.union_right]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ h.union_left, ih₂ h.union_right]
  | lt e₁ e₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ h.union_left, ih₂ h.union_right]
  | eq e₁ e₂ ih₁ ih₂ =>
    simp only [eval]
    rw [ih₁ h.union_left, ih₂ h.union_right]

theorem eval_agree_of_subset {e : Expr} {L : VarSet} {σ₁ σ₂ : State}
    (hL : freeVars e ⊆ L) (h : Agree L σ₁ σ₂) : eval σ₁ e = eval σ₂ e :=
  eval_agree (h.mono hL)

namespace Stmt

def vars : Stmt → VarSet
  | skip => []
  | assign x e => [x] ∪ freeVars e
  | seq s₁ s₂ => s₁.vars ∪ s₂.vars
  | ite e s₁ s₂ => freeVars e ∪ s₁.vars ∪ s₂.vars
  | .while e s => freeVars e ∪ s.vars

end Stmt

end Liveness
