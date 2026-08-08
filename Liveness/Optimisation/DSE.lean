import Liveness.Analysis.Transfer

namespace Liveness

open VarSet

def dse : Stmt → VarSet → Stmt × VarSet
  | .skip, L => (.skip, L)
  | .assign x e, L =>
    if x ∈ L then (.assign x e, remove x L ∪ freeVars e) else (.skip, L)
  | .seq s₁ s₂, L =>
    let r₂ := dse s₂ L
    let r₁ := dse s₁ r₂.2
    (.seq r₁.1 r₂.1, r₁.2)
  | .ite e s₁ s₂, L =>
    let r₁ := dse s₁ L
    let r₂ := dse s₂ L
    (.ite e r₁.1 r₂.1, freeVars e ∪ r₁.2 ∪ r₂.2)
  | .while e s, L =>
    let X := liveIn (.while e s) L
    (.while e (dse s X).1, X)

def optimise (s : Stmt) (L : VarSet) : Stmt := (dse s L).1

theorem dse_liveIn (s : Stmt) (L : VarSet) : (dse s L).2 = liveIn s L := by
  induction s generalizing L with
  | skip => rfl
  | assign x e =>
    rw [liveIn_assign]
    unfold dse
    split <;> rfl
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [dse, liveIn_seq]
    rw [ih₂, ih₁]
  | ite e s₁ s₂ ih₁ ih₂ =>
    simp only [dse, liveIn_ite]
    rw [ih₁, ih₂]
  | «while» e s _ => rfl

@[simp] theorem optimise_skip (L : VarSet) : optimise .skip L = .skip := rfl

theorem optimise_assign (x : String) (e : Expr) (L : VarSet) :
    optimise (.assign x e) L = if x ∈ L then .assign x e else .skip := by
  unfold optimise dse
  split <;> rfl

theorem optimise_assign_live {x : String} {e : Expr} {L : VarSet} (h : x ∈ L) :
    optimise (.assign x e) L = .assign x e := by
  rw [optimise_assign]; simp [h]

theorem optimise_assign_dead {x : String} {e : Expr} {L : VarSet} (h : x ∉ L) :
    optimise (.assign x e) L = .skip := by
  rw [optimise_assign]; simp [h]

@[simp] theorem optimise_seq (s₁ s₂ : Stmt) (L : VarSet) :
    optimise (.seq s₁ s₂) L = .seq (optimise s₁ (liveIn s₂ L)) (optimise s₂ L) := by
  unfold optimise
  simp only [dse, dse_liveIn]

@[simp] theorem optimise_ite (e : Expr) (s₁ s₂ : Stmt) (L : VarSet) :
    optimise (.ite e s₁ s₂) L = .ite e (optimise s₁ L) (optimise s₂ L) := rfl

@[simp] theorem optimise_while (e : Expr) (s : Stmt) (L : VarSet) :
    optimise (.while e s) L = .while e (optimise s (liveIn (.while e s) L)) := rfl

theorem optimise_vars_subset (s : Stmt) (L : VarSet) : (optimise s L).vars ⊆ s.vars := by
  induction s generalizing L with
  | skip => exact List.Subset.refl _
  | assign x e =>
    rw [optimise_assign]
    split
    · exact List.Subset.refl _
    · exact List.nil_subset _
  | seq s₁ s₂ ih₁ ih₂ =>
    rw [optimise_seq]
    exact union_mono (ih₁ _) (ih₂ _)
  | ite e s₁ s₂ ih₁ ih₂ =>
    rw [optimise_ite]
    exact union_mono (union_mono (List.Subset.refl _) (ih₁ _)) (ih₂ _)
  | «while» e s ih =>
    rw [optimise_while]
    exact union_mono (List.Subset.refl _) (ih _)

theorem optimise_size_le (s : Stmt) (L : VarSet) : (optimise s L).size ≤ s.size := by
  induction s generalizing L with
  | skip => exact Nat.le_refl _
  | assign x e =>
    rw [optimise_assign]
    split <;> simp [Stmt.size]
  | seq s₁ s₂ ih₁ ih₂ =>
    rw [optimise_seq]
    simp only [Stmt.size]
    have := ih₁ (liveIn s₂ L)
    have := ih₂ L
    omega
  | ite e s₁ s₂ ih₁ ih₂ =>
    rw [optimise_ite]
    simp only [Stmt.size]
    have := ih₁ L
    have := ih₂ L
    omega
  | «while» e s ih =>
    rw [optimise_while]
    simp only [Stmt.size]
    have := ih (liveIn (.while e s) L)
    omega

theorem optimise_congr (s : Stmt) {L₁ L₂ : VarSet} (h : Equiv L₁ L₂) :
    optimise s L₁ = optimise s L₂ := by
  induction s generalizing L₁ L₂ with
  | skip => rfl
  | assign x e =>
    rw [optimise_assign, optimise_assign]
    by_cases hx : x ∈ L₁
    · simp [hx, h.mem_iff.1 hx]
    · have hx₂ : x ∉ L₂ := fun h' => hx (h.mem_iff.2 h')
      simp [hx, hx₂]
  | seq s₁ s₂ ih₁ ih₂ =>
    rw [optimise_seq, optimise_seq, ih₂ h, ih₁ (liveIn_equiv h)]
  | ite e s₁ s₂ ih₁ ih₂ =>
    rw [optimise_ite, optimise_ite, ih₁ h, ih₂ h]
  | «while» e s ih =>
    rw [optimise_while, optimise_while, ih (liveIn_equiv h)]

end Liveness
