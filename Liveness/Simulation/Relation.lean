import Liveness.Optimisation.DSE

namespace Liveness

def Match (L : VarSet) (c₁ c₂ : Config) : Prop :=
  c₂.1 = optimise c₁.1 L ∧ Agree (liveIn c₁.1 L) c₁.2 c₂.2

namespace Match

theorem init (L : VarSet) (s : Stmt) (σ : State) : Match L (s, σ) (optimise s L, σ) :=
  ⟨rfl, Agree.refl _ σ⟩

theorem skip_target {L : VarSet} {σ₁ σ₂ : State} {t : Stmt} (h : Match L (.skip, σ₁) (t, σ₂)) :
    t = .skip ∧ Agree L σ₁ σ₂ :=
  ⟨h.1, by simpa using h.2⟩

end Match

theorem step_simulation {L : VarSet} {c₁ c₁' c₂ : Config}
    (hm : Match L c₁ c₂) (hs : Step c₁ c₁') :
    ∃ c₂', Match L c₁' c₂' ∧ (Step c₂ c₂' ∨ (c₂' = c₂ ∧ c₁'.1.size < c₁.1.size)) := by
  induction hs generalizing L c₂ with
  | assign x e σ =>
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only at ht ha
    by_cases hx : x ∈ L
    · rw [optimise_assign_live hx] at ht
      rw [liveIn_assign_live hx] at ha
      subst ht
      refine ⟨(.skip, σ₂.update x (eval σ₂ e)), ⟨rfl, ?_⟩, Or.inl (Step.assign x e σ₂)⟩
      simp only [liveIn_skip]
      rw [eval_agree ha.union_right]
      exact Agree.update_same_value x _ ha.union_left
    · rw [optimise_assign_dead hx] at ht
      rw [liveIn_assign_dead hx] at ha
      subst ht
      refine ⟨(.skip, σ₂), ⟨rfl, ?_⟩, Or.inr ⟨rfl, by simp [Stmt.size]⟩⟩
      simp only [liveIn_skip]
      exact Agree.update_dead_left _ hx ha
  | seqSkip s σ =>
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only [optimise_seq, optimise_skip, liveIn_seq, liveIn_skip] at ht ha
    subst ht
    exact ⟨(optimise s L, σ₂), ⟨rfl, ha⟩, Or.inl (Step.seqSkip _ σ₂)⟩
  | seqStep s₂ h ih =>
    rename_i s₁ s₁' σ σ'
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only [optimise_seq, liveIn_seq] at ht ha
    subst ht
    obtain ⟨⟨t₁', σ₂'⟩, hm', hcase⟩ :=
      ih (L := liveIn s₂ L) (c₂ := (optimise s₁ (liveIn s₂ L), σ₂)) ⟨rfl, ha⟩
    refine ⟨(.seq t₁' (optimise s₂ L), σ₂'), ⟨?_, ?_⟩, ?_⟩
    · have h₁ : t₁' = optimise s₁' (liveIn s₂ L) := hm'.1
      simp only [optimise_seq, h₁]
    · exact hm'.2
    · rcases hcase with hstep | ⟨heq, hlt⟩
      · exact Or.inl (Step.seqStep _ hstep)
      · cases heq
        refine Or.inr ⟨rfl, ?_⟩
        simp only [Stmt.size] at hlt ⊢
        omega
  | iteTrue s₁ s₂ h =>
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only [optimise_ite, liveIn_ite] at ht ha
    subst ht
    have hev := eval_agree ha.union_left.union_left
    exact ⟨(optimise s₁ L, σ₂), ⟨rfl, ha.union_left.union_right⟩,
      Or.inl (Step.iteTrue _ _ (hev ▸ h))⟩
  | iteFalse s₁ s₂ h =>
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only [optimise_ite, liveIn_ite] at ht ha
    subst ht
    have hev := eval_agree ha.union_left.union_left
    exact ⟨(optimise s₂ L, σ₂), ⟨rfl, ha.union_right⟩,
      Or.inl (Step.iteFalse _ _ (hev ▸ h))⟩
  | whileUnfold e s σ =>
    obtain ⟨t, σ₂⟩ := c₂
    obtain ⟨ht, ha⟩ := hm
    simp only [optimise_while] at ht
    simp only at ha
    subst ht
    refine ⟨(.ite e (.seq (optimise s (liveIn (.while e s) L)) (.while e (optimise s (liveIn (.while e s) L)))) .skip, σ₂),
      ⟨?_, ?_⟩, Or.inl (Step.whileUnfold _ _ σ₂)⟩
    · simp only [optimise_ite, optimise_seq, optimise_while, optimise_skip]
    · simp only [liveIn_ite, liveIn_seq, liveIn_skip]
      exact Agree.union
        (Agree.union (ha.mono (liveIn_while_cond e s L)) (ha.mono (liveIn_while_body e s L)))
        (ha.mono (liveIn_while_out e s L))

end Liveness
