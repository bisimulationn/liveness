import Liveness.Optimisation.DSE
import Liveness.Analysis.Soundness

namespace Liveness

theorem dse_bigStep_forward {s : Stmt} {σ₁ σ₁' : State} (h : BigStep s σ₁ σ₁') :
    ∀ {L : VarSet} {σ₂ : State}, Agree (liveIn s L) σ₁ σ₂ →
      ∃ σ₂', BigStep (optimise s L) σ₂ σ₂' ∧ Agree L σ₁' σ₂' := by
  induction h with
  | skip σ =>
    intro L σ₂ ha
    exact ⟨σ₂, BigStep.skip σ₂, by simpa using ha⟩
  | assign x e σ =>
    intro L σ₂ ha
    by_cases hx : x ∈ L
    · rw [liveIn_assign_live hx] at ha
      refine ⟨_, optimise_assign_live hx ▸ BigStep.assign x e σ₂, ?_⟩
      rw [eval_agree ha.union_right]
      exact Agree.update_same_value x _ ha.union_left
    · rw [liveIn_assign_dead hx] at ha
      exact ⟨σ₂, optimise_assign_dead hx ▸ BigStep.skip σ₂, Agree.update_dead_left _ hx ha⟩
  | seq _ _ ih₁ ih₂ =>
    intro L σ₂ ha
    obtain ⟨σ₂', hb₁, ha₁⟩ := ih₁ ha
    obtain ⟨σ₂'', hb₂, ha₂⟩ := ih₂ ha₁
    exact ⟨σ₂'', optimise_seq _ _ _ ▸ BigStep.seq hb₁ hb₂, ha₂⟩
  | iteTrue he _ ih =>
    intro L σ₂ ha
    rw [liveIn_ite] at ha
    have hev := eval_agree ha.union_left.union_left
    obtain ⟨σ₂', hb, ha'⟩ := ih ha.union_left.union_right
    exact ⟨σ₂', optimise_ite _ _ _ _ ▸ BigStep.iteTrue (hev ▸ he) hb, ha'⟩
  | iteFalse he _ ih =>
    intro L σ₂ ha
    rw [liveIn_ite] at ha
    have hev := eval_agree ha.union_left.union_left
    obtain ⟨σ₂', hb, ha'⟩ := ih ha.union_right
    exact ⟨σ₂', optimise_ite _ _ _ _ ▸ BigStep.iteFalse (hev ▸ he) hb, ha'⟩
  | whileFalse he =>
    intro L σ₂ ha
    have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
    exact ⟨σ₂, optimise_while _ _ _ ▸ BigStep.whileFalse (hev ▸ he),
      ha.mono (liveIn_while_out _ _ L)⟩
  | whileTrue he _ _ ihb ihw =>
    intro L σ₂ ha
    have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
    obtain ⟨σ₂', hb, ha'⟩ := ihb (ha.mono (liveIn_while_body _ _ L))
    obtain ⟨σ₂'', hw, ha''⟩ := ihw ha'
    rw [optimise_while] at hw
    exact ⟨σ₂'', optimise_while _ _ _ ▸ BigStep.whileTrue (hev ▸ he) hb hw, ha''⟩

theorem dse_bigStep_backward {t : Stmt} {σ₂ σ₂' : State} (h : BigStep t σ₂ σ₂') :
    ∀ {s : Stmt} {L : VarSet} {σ₁ : State}, t = optimise s L → Agree (liveIn s L) σ₁ σ₂ →
      ∃ σ₁', BigStep s σ₁ σ₁' ∧ Agree L σ₁' σ₂' := by
  induction h with
  | skip σ =>
    intro s L σ₁ ht ha
    cases s with
    | skip => exact ⟨σ₁, BigStep.skip σ₁, by simpa using ha⟩
    | assign x e =>
      by_cases hx : x ∈ L
      · rw [optimise_assign_live hx] at ht; cases ht
      · rw [liveIn_assign_dead hx] at ha
        exact ⟨_, BigStep.assign x e σ₁, Agree.update_dead_left _ hx ha⟩
    | seq => rw [optimise_seq] at ht; cases ht
    | ite => rw [optimise_ite] at ht; cases ht
    | «while» => rw [optimise_while] at ht; cases ht
  | assign x e σ =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht
        cases ht
        rw [liveIn_assign_live hy] at ha
        refine ⟨_, BigStep.assign x e σ₁, ?_⟩
        rw [eval_agree ha.union_right]
        exact Agree.update_same_value x _ ha.union_left
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq => rw [optimise_seq] at ht; cases ht
    | ite => rw [optimise_ite] at ht; cases ht
    | «while» => rw [optimise_while] at ht; cases ht
  | seq _ _ ih₁ ih₂ =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht; cases ht
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq s₁ s₂ =>
      rw [optimise_seq] at ht
      cases ht
      obtain ⟨σ₁', hb₁, ha₁⟩ := ih₁ rfl ha
      obtain ⟨σ₁'', hb₂, ha₂⟩ := ih₂ rfl ha₁
      exact ⟨σ₁'', BigStep.seq hb₁ hb₂, ha₂⟩
    | ite => rw [optimise_ite] at ht; cases ht
    | «while» => rw [optimise_while] at ht; cases ht
  | iteTrue he _ ih =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht; cases ht
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq => rw [optimise_seq] at ht; cases ht
    | ite e' s₁ s₂ =>
      rw [optimise_ite] at ht
      cases ht
      rw [liveIn_ite] at ha
      have hev := eval_agree ha.union_left.union_left
      obtain ⟨σ₁', hb, ha'⟩ := ih rfl ha.union_left.union_right
      exact ⟨σ₁', BigStep.iteTrue (hev.symm ▸ he) hb, ha'⟩
    | «while» => rw [optimise_while] at ht; cases ht
  | iteFalse he _ ih =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht; cases ht
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq => rw [optimise_seq] at ht; cases ht
    | ite e' s₁ s₂ =>
      rw [optimise_ite] at ht
      cases ht
      rw [liveIn_ite] at ha
      have hev := eval_agree ha.union_left.union_left
      obtain ⟨σ₁', hb, ha'⟩ := ih rfl ha.union_right
      exact ⟨σ₁', BigStep.iteFalse (hev.symm ▸ he) hb, ha'⟩
    | «while» => rw [optimise_while] at ht; cases ht
  | whileFalse he =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht; cases ht
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq => rw [optimise_seq] at ht; cases ht
    | ite => rw [optimise_ite] at ht; cases ht
    | «while» e' s =>
      rw [optimise_while] at ht
      cases ht
      have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
      exact ⟨σ₁, BigStep.whileFalse (hev.symm ▸ he), ha.mono (liveIn_while_out _ _ L)⟩
  | whileTrue he _ _ ihb ihw =>
    intro s L σ₁ ht ha
    cases s with
    | skip => cases ht
    | assign y e' =>
      by_cases hy : y ∈ L
      · rw [optimise_assign_live hy] at ht; cases ht
      · rw [optimise_assign_dead hy] at ht; cases ht
    | seq => rw [optimise_seq] at ht; cases ht
    | ite => rw [optimise_ite] at ht; cases ht
    | «while» e' s =>
      rw [optimise_while] at ht
      cases ht
      have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
      obtain ⟨σ₁', hb, ha'⟩ := ihb rfl (ha.mono (liveIn_while_body _ _ L))
      obtain ⟨σ₁'', hw, ha''⟩ := ihw (optimise_while _ s L).symm ha'
      exact ⟨σ₁'', BigStep.whileTrue (hev.symm ▸ he) hb hw, ha''⟩

theorem dse_correct_general (s : Stmt) (L : VarSet) {σ₁ σ₂ : State}
    (ha : Agree (liveIn s L) σ₁ σ₂) :
    (∀ σ₁', Terminates s σ₁ σ₁' → ∃ σ₂', Terminates (optimise s L) σ₂ σ₂' ∧ Agree L σ₁' σ₂') ∧
    (∀ σ₂', Terminates (optimise s L) σ₂ σ₂' → ∃ σ₁', Terminates s σ₁ σ₁' ∧ Agree L σ₁' σ₂') := by
  constructor
  · intro σ₁' h
    obtain ⟨σ₂', hb, ha'⟩ := dse_bigStep_forward (BigStep.of_terminates h) ha
    exact ⟨σ₂', hb.terminates, ha'⟩
  · intro σ₂' h
    obtain ⟨σ₁', hb, ha'⟩ := dse_bigStep_backward (BigStep.of_terminates h) rfl ha
    exact ⟨σ₁', hb.terminates, ha'⟩

theorem dse_correct (s : Stmt) (L : VarSet) : ObsEquiv L s (optimise s L) :=
  fun σ => dse_correct_general s L (Agree.refl _ σ)

theorem dse_preserves_termination (s : Stmt) (L : VarSet) (σ : State) :
    (∃ σ', Terminates s σ σ') ↔ (∃ σ', Terminates (optimise s L) σ σ') := by
  obtain ⟨hf, hb⟩ := dse_correct s L σ
  exact ⟨fun ⟨σ', h⟩ => let ⟨σ'', h', _⟩ := hf σ' h; ⟨σ'', h'⟩,
    fun ⟨σ', h⟩ => let ⟨σ'', h', _⟩ := hb σ' h; ⟨σ'', h'⟩⟩

theorem dse_preserves_divergence (s : Stmt) (L : VarSet) (σ : State) :
    Diverges (s, σ) ↔ Diverges (optimise s L, σ) :=
  (dse_correct s L).diverges_iff σ

theorem dse_final_agree (s : Stmt) (L : VarSet) {σ σ₁ σ₂ : State}
    (h₁ : Terminates s σ σ₁) (h₂ : Terminates (optimise s L) σ σ₂) : Agree L σ₁ σ₂ := by
  obtain ⟨σ₂', h₂', ha⟩ := ((dse_correct s L) σ).1 σ₁ h₁
  rw [Terminates.unique h₂ h₂']
  exact ha

end Liveness
