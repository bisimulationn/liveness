import Liveness.Semantics
import Liveness.VarSet

namespace Liveness

def Agree (L : VarSet) (σ₁ σ₂ : State) : Prop := ∀ x, x ∈ L → σ₁ x = σ₂ x

namespace Agree

theorem refl (L : VarSet) (σ : State) : Agree L σ σ := fun _ _ => rfl

theorem symm {L : VarSet} {σ₁ σ₂ : State} (h : Agree L σ₁ σ₂) : Agree L σ₂ σ₁ :=
  fun x hx => (h x hx).symm

theorem trans {L : VarSet} {σ₁ σ₂ σ₃ : State} (h₁ : Agree L σ₁ σ₂) (h₂ : Agree L σ₂ σ₃) :
    Agree L σ₁ σ₃ :=
  fun x hx => (h₁ x hx).trans (h₂ x hx)

theorem mono {L L' : VarSet} {σ₁ σ₂ : State} (hL : L' ⊆ L) (h : Agree L σ₁ σ₂) : Agree L' σ₁ σ₂ :=
  fun x hx => h x (hL hx)

theorem union {L₁ L₂ : VarSet} {σ₁ σ₂ : State} (h₁ : Agree L₁ σ₁ σ₂) (h₂ : Agree L₂ σ₁ σ₂) :
    Agree (L₁ ∪ L₂) σ₁ σ₂ := by
  intro x hx
  rcases VarSet.mem_union.1 hx with h | h
  · exact h₁ x h
  · exact h₂ x h

theorem union_left {L₁ L₂ : VarSet} {σ₁ σ₂ : State} (h : Agree (L₁ ∪ L₂) σ₁ σ₂) : Agree L₁ σ₁ σ₂ :=
  h.mono (VarSet.subset_union_left _ _)

theorem union_right {L₁ L₂ : VarSet} {σ₁ σ₂ : State} (h : Agree (L₁ ∪ L₂) σ₁ σ₂) : Agree L₂ σ₁ σ₂ :=
  h.mono (VarSet.subset_union_right _ _)

theorem update_same_value {L : VarSet} {σ₁ σ₂ : State} (x : String) (v : Int)
    (h : Agree (VarSet.remove x L) σ₁ σ₂) : Agree L (σ₁.update x v) (σ₂.update x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp
  · rw [State.update_other _ _ hyx, State.update_other _ _ hyx]
    exact h y (VarSet.mem_remove.2 ⟨hy, hyx⟩)

theorem update_dead_left {L : VarSet} {σ₁ σ₂ : State} {x : String} (v : Int)
    (hx : x ∉ L) (h : Agree L σ₁ σ₂) : Agree L (σ₁.update x v) σ₂ := by
  intro y hy
  have hyx : y ≠ x := fun hyx => hx (hyx ▸ hy)
  rw [State.update_other _ _ hyx]
  exact h y hy

theorem update_dead_right {L : VarSet} {σ₁ σ₂ : State} {x : String} (v : Int)
    (hx : x ∉ L) (h : Agree L σ₁ σ₂) : Agree L σ₁ (σ₂.update x v) :=
  (update_dead_left v hx h.symm).symm

end Agree

def ObsEquiv (L : VarSet) (s t : Stmt) : Prop :=
  ∀ σ,
    (∀ σ₁, Terminates s σ σ₁ → ∃ σ₂, Terminates t σ σ₂ ∧ Agree L σ₁ σ₂) ∧
    (∀ σ₂, Terminates t σ σ₂ → ∃ σ₁, Terminates s σ σ₁ ∧ Agree L σ₁ σ₂)

namespace ObsEquiv

theorem refl (L : VarSet) (s : Stmt) : ObsEquiv L s s :=
  fun _ => ⟨fun σ₁ h => ⟨σ₁, h, Agree.refl L σ₁⟩, fun σ₂ h => ⟨σ₂, h, Agree.refl L σ₂⟩⟩

theorem symm {L : VarSet} {s t : Stmt} (h : ObsEquiv L s t) : ObsEquiv L t s := by
  intro σ
  obtain ⟨h₁, h₂⟩ := h σ
  exact ⟨fun σ₂ ht => let ⟨σ₁, hs, ha⟩ := h₂ σ₂ ht; ⟨σ₁, hs, ha.symm⟩,
    fun σ₁ hs => let ⟨σ₂, ht, ha⟩ := h₁ σ₁ hs; ⟨σ₂, ht, ha.symm⟩⟩

theorem trans {L : VarSet} {s t u : Stmt} (h₁ : ObsEquiv L s t) (h₂ : ObsEquiv L t u) :
    ObsEquiv L s u := by
  intro σ
  obtain ⟨h₁f, h₁b⟩ := h₁ σ
  obtain ⟨h₂f, h₂b⟩ := h₂ σ
  constructor
  · intro σ₁ hs
    obtain ⟨σ₂, ht, ha⟩ := h₁f σ₁ hs
    obtain ⟨σ₃, hu, ha'⟩ := h₂f σ₂ ht
    exact ⟨σ₃, hu, ha.trans ha'⟩
  · intro σ₃ hu
    obtain ⟨σ₂, ht, ha⟩ := h₂b σ₃ hu
    obtain ⟨σ₁, hs, ha'⟩ := h₁b σ₂ ht
    exact ⟨σ₁, hs, ha'.trans ha⟩

theorem mono {L L' : VarSet} {s t : Stmt} (hL : L' ⊆ L) (h : ObsEquiv L s t) : ObsEquiv L' s t := by
  intro σ
  obtain ⟨hf, hb⟩ := h σ
  exact ⟨fun σ₁ hs => let ⟨σ₂, ht, ha⟩ := hf σ₁ hs; ⟨σ₂, ht, ha.mono hL⟩,
    fun σ₂ ht => let ⟨σ₁, hs, ha⟩ := hb σ₂ ht; ⟨σ₁, hs, ha.mono hL⟩⟩

theorem diverges_iff {L : VarSet} {s t : Stmt} (h : ObsEquiv L s t) (σ : State) :
    Diverges (s, σ) ↔ Diverges (t, σ) := by
  rw [diverges_iff_not_terminates, diverges_iff_not_terminates]
  obtain ⟨hf, hb⟩ := h σ
  constructor
  · rintro hns ⟨σ₂, ht⟩
    obtain ⟨σ₁, hs, _⟩ := hb σ₂ ht
    exact hns ⟨σ₁, hs⟩
  · rintro hnt ⟨σ₁, hs⟩
    obtain ⟨σ₂, ht, _⟩ := hf σ₁ hs
    exact hnt ⟨σ₂, ht⟩

end ObsEquiv

end Liveness
