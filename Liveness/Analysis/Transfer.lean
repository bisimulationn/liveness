import Liveness.FreeVars
import Liveness.Analysis.FixedPoint

namespace Liveness

open VarSet

def liveInB : (s : Stmt) → (L : VarSet) → { X : VarSet // X ⊆ L ∪ s.vars }
  | .skip, L => ⟨L, subset_union_left _ _⟩
  | .assign x e, L =>
    if x ∈ L then
      ⟨remove x L ∪ freeVars e,
        union_subset (subset_union_of_left (remove_subset x L))
          (subset_union_of_right (subset_union_right _ _))⟩
    else ⟨L, subset_union_left _ _⟩
  | .seq s₁ s₂, L =>
    let r₂ := liveInB s₂ L
    let r₁ := liveInB s₁ r₂.1
    ⟨r₁.1, List.Subset.trans r₁.2 (union_subset
      (List.Subset.trans r₂.2 (union_mono (List.Subset.refl L) (subset_union_right _ _)))
      (subset_union_of_right (subset_union_left _ _)))⟩
  | .ite e s₁ s₂, L =>
    let r₁ := liveInB s₁ L
    let r₂ := liveInB s₂ L
    ⟨freeVars e ∪ r₁.1 ∪ r₂.1,
      union_subset
        (union_subset
          (subset_union_of_right (subset_union_of_left (subset_union_left _ _)))
          (List.Subset.trans r₁.2
            (union_mono (List.Subset.refl L)
              (subset_union_of_left (subset_union_right _ _)))))
        (List.Subset.trans r₂.2 (union_mono (List.Subset.refl L) (subset_union_right _ _)))⟩
  | .while e s, L =>
    ⟨lfp (L ∪ (freeVars e ∪ s.vars)) (fun X => L ∪ freeVars e ∪ (liveInB s X).1)
        (fun X hX =>
          union_subset
            (union_subset (subset_union_left _ _)
              (subset_union_of_right (subset_union_left _ _)))
            (List.Subset.trans (liveInB s X).2
              (union_subset hX (subset_union_of_right (subset_union_right _ _))))),
      lfp_subset_universe _⟩

def liveIn (s : Stmt) (L : VarSet) : VarSet := (liveInB s L).1

theorem liveIn_subset (s : Stmt) (L : VarSet) : liveIn s L ⊆ L ∪ s.vars := (liveInB s L).2

@[simp] theorem liveIn_skip (L : VarSet) : liveIn .skip L = L := rfl

theorem liveIn_assign (x : String) (e : Expr) (L : VarSet) :
    liveIn (.assign x e) L = if x ∈ L then remove x L ∪ freeVars e else L := by
  unfold liveIn liveInB
  split <;> rfl

theorem liveIn_assign_live {x : String} {e : Expr} {L : VarSet} (h : x ∈ L) :
    liveIn (.assign x e) L = remove x L ∪ freeVars e := by
  rw [liveIn_assign]; simp [h]

theorem liveIn_assign_dead {x : String} {e : Expr} {L : VarSet} (h : x ∉ L) :
    liveIn (.assign x e) L = L := by
  rw [liveIn_assign]; simp [h]

@[simp] theorem liveIn_seq (s₁ s₂ : Stmt) (L : VarSet) :
    liveIn (.seq s₁ s₂) L = liveIn s₁ (liveIn s₂ L) := rfl

@[simp] theorem liveIn_ite (e : Expr) (s₁ s₂ : Stmt) (L : VarSet) :
    liveIn (.ite e s₁ s₂) L = freeVars e ∪ liveIn s₁ L ∪ liveIn s₂ L := rfl

def loopFunctional (e : Expr) (s : Stmt) (L : VarSet) (X : VarSet) : VarSet :=
  L ∪ freeVars e ∪ liveIn s X

theorem loopFunctional_bounded (e : Expr) (s : Stmt) (L : VarSet) :
    Bounded (L ∪ (freeVars e ∪ s.vars)) (loopFunctional e s L) :=
  fun X hX =>
    union_subset
      (union_subset (subset_union_left _ _) (subset_union_of_right (subset_union_left _ _)))
      (List.Subset.trans (liveIn_subset s X)
        (union_subset hX (subset_union_of_right (subset_union_right _ _))))

theorem liveIn_while (e : Expr) (s : Stmt) (L : VarSet) :
    liveIn (.while e s) L =
      lfp (L ∪ (freeVars e ∪ s.vars)) (loopFunctional e s L) (loopFunctional_bounded e s L) := rfl

theorem liveIn_mono (s : Stmt) : Monotone (liveIn s) := by
  induction s with
  | skip => intro A B h; simpa using h
  | assign x e =>
    intro A B h
    by_cases hA : x ∈ A
    · rw [liveIn_assign_live hA, liveIn_assign_live (h hA)]
      exact union_mono (remove_mono x h) (List.Subset.refl _)
    · rw [liveIn_assign_dead hA]
      by_cases hB : x ∈ B
      · rw [liveIn_assign_live hB]
        intro y hy
        have hyx : y ≠ x := fun hyx => hA (hyx ▸ hy)
        exact mem_union.2 (Or.inl (mem_remove.2 ⟨h hy, hyx⟩))
      · rw [liveIn_assign_dead hB]; exact h
  | seq s₁ s₂ ih₁ ih₂ =>
    intro A B h
    simp only [liveIn_seq]
    exact ih₁ _ _ (ih₂ _ _ h)
  | ite e s₁ s₂ ih₁ ih₂ =>
    intro A B h
    simp only [liveIn_ite]
    exact union_mono (union_mono (List.Subset.refl _) (ih₁ _ _ h)) (ih₂ _ _ h)
  | «while» e s ih =>
    intro A B h
    rw [liveIn_while, liveIn_while]
    apply lfp_mono
    · intro X Y hXY
      exact union_mono (List.Subset.refl _) (ih _ _ hXY)
    · intro X
      exact union_mono (union_mono h (List.Subset.refl _)) (List.Subset.refl _)

theorem loopFunctional_mono (e : Expr) (s : Stmt) (L : VarSet) : Monotone (loopFunctional e s L) :=
  fun _ _ h => union_mono (List.Subset.refl _) (liveIn_mono s _ _ h)

theorem liveIn_while_postfixed (e : Expr) (s : Stmt) (L : VarSet) :
    L ∪ freeVars e ∪ liveIn s (liveIn (.while e s) L) ⊆ liveIn (.while e s) L := by
  rw [liveIn_while]
  exact lfp_postfixed (loopFunctional_bounded e s L)

theorem liveIn_while_fixed (e : Expr) (s : Stmt) (L : VarSet) :
    Equiv (L ∪ freeVars e ∪ liveIn s (liveIn (.while e s) L)) (liveIn (.while e s) L) := by
  rw [liveIn_while]
  exact lfp_fixed (loopFunctional_bounded e s L) (loopFunctional_mono e s L)

theorem liveIn_while_least (e : Expr) (s : Stmt) (L : VarSet) {Y : VarSet}
    (hY : L ∪ freeVars e ∪ liveIn s Y ⊆ Y) : liveIn (.while e s) L ⊆ Y := by
  rw [liveIn_while]
  exact lfp_least (loopFunctional_bounded e s L) (loopFunctional_mono e s L) hY

theorem liveIn_while_out (e : Expr) (s : Stmt) (L : VarSet) : L ⊆ liveIn (.while e s) L :=
  List.Subset.trans (subset_union_of_left (subset_union_left _ _)) (liveIn_while_postfixed e s L)

theorem liveIn_while_cond (e : Expr) (s : Stmt) (L : VarSet) : freeVars e ⊆ liveIn (.while e s) L :=
  List.Subset.trans (subset_union_of_left (subset_union_right _ _)) (liveIn_while_postfixed e s L)

theorem liveIn_while_body (e : Expr) (s : Stmt) (L : VarSet) :
    liveIn s (liveIn (.while e s) L) ⊆ liveIn (.while e s) L :=
  List.Subset.trans (subset_union_right _ _) (liveIn_while_postfixed e s L)

theorem liveIn_while_equiv_of (e : Expr) (s : Stmt) (L : VarSet) {Y : VarSet}
    (hY : L ∪ freeVars e ∪ liveIn s Y ⊆ Y) (hle : Y ⊆ L ∪ freeVars e) :
    Equiv (liveIn (.while e s) L) Y :=
  ⟨liveIn_while_least e s L hY,
    List.Subset.trans hle (union_subset (liveIn_while_out e s L) (liveIn_while_cond e s L))⟩

theorem liveIn_equiv {s : Stmt} {L₁ L₂ : VarSet} (h : Equiv L₁ L₂) :
    Equiv (liveIn s L₁) (liveIn s L₂) :=
  ⟨liveIn_mono s _ _ h.1, liveIn_mono s _ _ h.2⟩

end Liveness
