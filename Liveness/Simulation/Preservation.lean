import Liveness.Simulation.Relation

namespace Liveness

theorem steps_simulation {L : VarSet} {c₁ c₁' c₂ : Config}
    (hs : Steps c₁ c₁') (hm : Match L c₁ c₂) : ∃ c₂', Steps c₂ c₂' ∧ Match L c₁' c₂' := by
  induction hs generalizing c₂ with
  | refl c => exact ⟨c₂, Steps.refl c₂, hm⟩
  | step h₁ _ ih =>
    obtain ⟨c₂', hm', hcase⟩ := step_simulation hm h₁
    obtain ⟨c₂'', hsteps, hm''⟩ := ih hm'
    rcases hcase with hstep | ⟨rfl, _⟩
    · exact ⟨c₂'', Steps.step hstep hsteps, hm''⟩
    · exact ⟨c₂'', hsteps, hm''⟩

theorem forward_terminates {L : VarSet} {s t : Stmt} {σ₁ σ₁' σ₂ : State}
    (ht : Terminates s σ₁ σ₁') (hm : Match L (s, σ₁) (t, σ₂)) :
    ∃ σ₂', Terminates t σ₂ σ₂' ∧ Agree L σ₁' σ₂' := by
  obtain ⟨⟨t', σ₂'⟩, hsteps, hm'⟩ := steps_simulation ht hm
  obtain ⟨rfl, ha⟩ := hm'.skip_target
  exact ⟨σ₂', hsteps, ha⟩

theorem diverges_step_target {L : VarSet} (c₁ c₂ : Config) (hd : Diverges c₁)
    (hm : Match L c₁ c₂) : ∃ c₁' c₂', Step c₂ c₂' ∧ Match L c₁' c₂' ∧ Diverges c₁' := by
  obtain ⟨c₁', hs⟩ := hd.can_step
  obtain ⟨c₂', hm', hcase⟩ := step_simulation hm hs
  rcases hcase with hstep | ⟨rfl, hlt⟩
  · exact ⟨c₁', c₂', hstep, hm', hd.step hs⟩
  · exact diverges_step_target c₁' c₂' (hd.step hs) hm'
termination_by c₁.1.size

theorem forward_diverges {L : VarSet} {c₁ c₂ : Config} (hd : Diverges c₁) (hm : Match L c₁ c₂) :
    Diverges c₂ := by
  intro n
  induction n generalizing c₁ c₂ with
  | zero => exact ⟨c₂, StepsN.zero c₂⟩
  | succ n ih =>
    obtain ⟨c₁', c₂', hstep, hm', hd'⟩ := diverges_step_target c₁ c₂ hd hm
    obtain ⟨c₂'', hn⟩ := ih hd' hm'
    exact ⟨c₂'', StepsN.succ hstep hn⟩

theorem backward_terminates {L : VarSet} {s t : Stmt} {σ₁ σ₂ σ₂' : State}
    (ht : Terminates t σ₂ σ₂') (hm : Match L (s, σ₁) (t, σ₂)) :
    ∃ σ₁', Terminates s σ₁ σ₁' ∧ Agree L σ₁' σ₂' := by
  rcases terminates_or_diverges s σ₁ with ⟨σ₁', hs⟩ | hd
  · obtain ⟨σ₂'', ht', ha⟩ := forward_terminates hs hm
    rw [Terminates.unique ht ht']
    exact ⟨σ₁', hs, ha⟩
  · exact absurd ht (forward_diverges hd hm).not_terminates

theorem dse_correct_sim (s : Stmt) (L : VarSet) : ObsEquiv L s (optimise s L) :=
  fun σ =>
    ⟨fun _ h => forward_terminates h (Match.init L s σ),
      fun _ h => backward_terminates h (Match.init L s σ)⟩

theorem dse_diverges_sim (s : Stmt) (L : VarSet) (σ : State) (hd : Diverges (s, σ)) :
    Diverges (optimise s L, σ) :=
  forward_diverges hd (Match.init L s σ)

end Liveness
