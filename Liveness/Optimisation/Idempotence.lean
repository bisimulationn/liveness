import Liveness.Optimisation.DSE

namespace Liveness

open VarSet

theorem liveIn_optimise (s : Stmt) :
    ∀ {X Y : VarSet}, Y ⊆ X → Equiv (liveIn (optimise s X) Y) (liveIn s Y) := by
  induction s with
  | skip => intro X Y _; exact Equiv.refl _
  | assign x e =>
    intro X Y hY
    by_cases hx : x ∈ X
    · rw [optimise_assign_live hx]; exact Equiv.refl _
    · rw [optimise_assign_dead hx, liveIn_skip, liveIn_assign_dead (fun h => hx (hY h))]
      exact Equiv.refl _
  | seq s₁ s₂ ih₁ ih₂ =>
    intro X Y hY
    rw [optimise_seq, liveIn_seq, liveIn_seq]
    have h₂ := ih₂ hY
    have hsub : liveIn (optimise s₂ X) Y ⊆ liveIn s₂ X :=
      List.Subset.trans h₂.1 (liveIn_mono s₂ _ _ hY)
    exact (ih₁ hsub).trans (liveIn_equiv h₂)
  | ite e s₁ s₂ ih₁ ih₂ =>
    intro X Y hY
    rw [optimise_ite, liveIn_ite, liveIn_ite]
    exact ((Equiv.refl _).union (ih₁ hY)).union (ih₂ hY)
  | «while» e s ih =>
    intro X Y hY
    rw [optimise_while]
    have hYX : liveIn (.while e s) Y ⊆ liveIn (.while e s) X := liveIn_mono _ _ _ hY
    have hfirst : liveIn (.while e (optimise s (liveIn (.while e s) X))) Y ⊆ liveIn (.while e s) Y := by
      apply liveIn_while_least
      exact List.Subset.trans (union_mono (List.Subset.refl _) (ih hYX).1)
        (liveIn_while_postfixed e s Y)
    refine ⟨hfirst, ?_⟩
    apply liveIn_while_least
    have hY'X : liveIn (.while e (optimise s (liveIn (.while e s) X))) Y ⊆ liveIn (.while e s) X :=
      List.Subset.trans hfirst hYX
    exact List.Subset.trans (union_mono (List.Subset.refl _) (ih hY'X).2)
      (liveIn_while_postfixed e _ Y)

theorem optimise_optimise (s : Stmt) :
    ∀ {X Y : VarSet}, Y ⊆ X → optimise (optimise s X) Y = optimise s Y := by
  induction s with
  | skip => intro X Y _; rfl
  | assign x e =>
    intro X Y hY
    by_cases hx : x ∈ X
    · rw [optimise_assign_live hx]
    · rw [optimise_assign_dead hx, optimise_skip, optimise_assign_dead (fun h => hx (hY h))]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro X Y hY
    rw [optimise_seq, optimise_seq, optimise_seq, ih₂ hY,
      optimise_congr _ (liveIn_optimise s₂ hY), ih₁ (liveIn_mono s₂ _ _ hY)]
  | ite e s₁ s₂ ih₁ ih₂ =>
    intro X Y hY
    rw [optimise_ite, optimise_ite, optimise_ite, ih₁ hY, ih₂ hY]
  | «while» e s ih =>
    intro X Y hY
    have hcongr := optimise_congr (optimise s (liveIn (.while e s) X))
      (liveIn_optimise (.while e s) hY)
    rw [optimise_while] at hcongr
    rw [optimise_while, optimise_while, optimise_while, hcongr, ih (liveIn_mono _ _ _ hY)]

theorem optimise_idem (s : Stmt) (L : VarSet) : optimise (optimise s L) L = optimise s L :=
  optimise_optimise s (List.Subset.refl L)

theorem liveIn_optimise_self (s : Stmt) (L : VarSet) :
    Equiv (liveIn (optimise s L) L) (liveIn s L) :=
  liveIn_optimise s (List.Subset.refl L)

end Liveness
