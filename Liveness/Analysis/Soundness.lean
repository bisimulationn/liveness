import Liveness.Analysis.Transfer

namespace Liveness

theorem liveness_sound {s : Stmt} {σ₁ σ₁' : State} (h₁ : BigStep s σ₁ σ₁') :
    ∀ {L : VarSet} {σ₂ σ₂' : State},
      Agree (liveIn s L) σ₁ σ₂ → BigStep s σ₂ σ₂' → Agree L σ₁' σ₂' := by
  induction h₁ with
  | skip σ =>
    intro L σ₂ σ₂' ha h₂
    cases h₂
    simpa using ha
  | assign x e σ =>
    intro L σ₂ σ₂' ha h₂
    cases h₂
    by_cases hx : x ∈ L
    · rw [liveIn_assign_live hx] at ha
      rw [eval_agree ha.union_right]
      exact Agree.update_same_value x _ ha.union_left
    · rw [liveIn_assign_dead hx] at ha
      exact Agree.update_dead_right _ hx (Agree.update_dead_left _ hx ha)
  | seq _ _ ih₁ ih₂ =>
    intro L σ₂ σ₂' ha h₂
    cases h₂ with
    | seq hc₁ hc₂ => exact ih₂ (ih₁ ha hc₁) hc₂
  | iteTrue he _ ih =>
    intro L σ₂ σ₂' ha h₂
    rw [liveIn_ite] at ha
    have hev := eval_agree ha.union_left.union_left
    cases h₂ with
    | iteTrue _ hc => exact ih ha.union_left.union_right hc
    | iteFalse he' _ => exact absurd (hev.trans he') he
  | iteFalse he _ ih =>
    intro L σ₂ σ₂' ha h₂
    rw [liveIn_ite] at ha
    have hev := eval_agree ha.union_left.union_left
    cases h₂ with
    | iteTrue he' _ => exact absurd (hev.symm.trans he) he'
    | iteFalse _ hc => exact ih ha.union_right hc
  | whileFalse he =>
    intro L σ₂ σ₂' ha h₂
    have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
    cases h₂ with
    | whileFalse => exact ha.mono (liveIn_while_out _ _ L)
    | whileTrue he' => exact absurd (hev.symm.trans he) he'
  | whileTrue he _ _ ihb ihw =>
    intro L σ₂ σ₂' ha h₂
    have hev := eval_agree_of_subset (liveIn_while_cond _ _ L) ha
    cases h₂ with
    | whileFalse he' => exact absurd (hev.trans he') he
    | whileTrue _ hc hw =>
      exact ihw (ihb (ha.mono (liveIn_while_body _ _ L)) hc) hw

end Liveness
