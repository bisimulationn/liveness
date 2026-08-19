import Liveness.Syntax
import Liveness.State

namespace Liveness

def eval (σ : State) : Expr → Int
  | .const n => n
  | .var x => σ x
  | .add e₁ e₂ => eval σ e₁ + eval σ e₂
  | .sub e₁ e₂ => eval σ e₁ - eval σ e₂
  | .mul e₁ e₂ => eval σ e₁ * eval σ e₂
  | .lt e₁ e₂ => if eval σ e₁ < eval σ e₂ then 1 else 0
  | .eq e₁ e₂ => if eval σ e₁ = eval σ e₂ then 1 else 0

abbrev Config := Stmt × State

inductive Step : Config → Config → Prop where
  | assign (x : String) (e : Expr) (σ : State) :
      Step (.assign x e, σ) (.skip, σ.update x (eval σ e))
  | seqSkip (s : Stmt) (σ : State) :
      Step (.seq .skip s, σ) (s, σ)
  | seqStep {s₁ s₁' : Stmt} {σ σ' : State} (s₂ : Stmt) (h : Step (s₁, σ) (s₁', σ')) :
      Step (.seq s₁ s₂, σ) (.seq s₁' s₂, σ')
  | iteTrue {e : Expr} {σ : State} (s₁ s₂ : Stmt) (h : eval σ e ≠ 0) :
      Step (.ite e s₁ s₂, σ) (s₁, σ)
  | iteFalse {e : Expr} {σ : State} (s₁ s₂ : Stmt) (h : eval σ e = 0) :
      Step (.ite e s₁ s₂, σ) (s₂, σ)
  | whileUnfold (e : Expr) (s : Stmt) (σ : State) :
      Step (.while e s, σ) (.ite e (.seq s (.while e s)) .skip, σ)

inductive Steps : Config → Config → Prop where
  | refl (c : Config) : Steps c c
  | step {c₁ c₂ c₃ : Config} (h₁ : Step c₁ c₂) (h₂ : Steps c₂ c₃) : Steps c₁ c₃

inductive StepsN : Nat → Config → Config → Prop where
  | zero (c : Config) : StepsN 0 c c
  | succ {n : Nat} {c₁ c₂ c₃ : Config} (h₁ : Step c₁ c₂) (h₂ : StepsN n c₂ c₃) :
      StepsN (n + 1) c₁ c₃

def Terminates (s : Stmt) (σ σ' : State) : Prop := Steps (s, σ) (.skip, σ')

def Diverges (c : Config) : Prop := ∀ n, ∃ c', StepsN n c c'

def InfiniteTrace (c : Config) : Prop :=
  ∃ f : Nat → Config, f 0 = c ∧ ∀ n, Step (f n) (f (n + 1))

theorem skip_stuck {σ : State} {c : Config} : ¬ Step (.skip, σ) c := by
  intro h
  cases h

theorem Step.deterministic {c c₁ c₂ : Config} (h₁ : Step c c₁) (h₂ : Step c c₂) : c₁ = c₂ := by
  induction h₁ generalizing c₂ with
  | assign x e σ => cases h₂; rfl
  | seqSkip s σ =>
    cases h₂ with
    | seqSkip => rfl
    | seqStep _ h => exact absurd h skip_stuck
  | seqStep s₂ h ih =>
    cases h₂ with
    | seqSkip => exact absurd h skip_stuck
    | seqStep _ h' => cases ih h'; rfl
  | iteTrue s₁ s₂ h =>
    cases h₂ with
    | iteTrue => rfl
    | iteFalse _ _ h' => exact absurd h' h
  | iteFalse s₁ s₂ h =>
    cases h₂ with
    | iteTrue _ _ h' => exact absurd h h'
    | iteFalse => rfl
  | whileUnfold e s σ => cases h₂; rfl

theorem progress (s : Stmt) (σ : State) (h : s ≠ .skip) : ∃ c', Step (s, σ) c' := by
  induction s generalizing σ with
  | skip => exact absurd rfl h
  | assign x e => exact ⟨_, Step.assign x e σ⟩
  | seq s₁ s₂ ih₁ _ =>
    by_cases h₁ : s₁ = .skip
    · subst h₁
      exact ⟨_, Step.seqSkip s₂ σ⟩
    · obtain ⟨⟨s₁', σ'⟩, hs⟩ := ih₁ σ h₁
      exact ⟨_, Step.seqStep s₂ hs⟩
  | ite e s₁ s₂ =>
    by_cases he : eval σ e = 0
    · exact ⟨_, Step.iteFalse s₁ s₂ he⟩
    · exact ⟨_, Step.iteTrue s₁ s₂ he⟩
  | «while» e s => exact ⟨_, Step.whileUnfold e s σ⟩

namespace Steps

theorem single {c c' : Config} (h : Step c c') : Steps c c' :=
  Steps.step h (Steps.refl c')

theorem trans {c₁ c₂ c₃ : Config} (h₁ : Steps c₁ c₂) (h₂ : Steps c₂ c₃) : Steps c₁ c₃ := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact Steps.step h (ih h₂)

theorem seq_congr {s₁ s₁' : Stmt} {σ σ' : State} (s₂ : Stmt)
    (h : Steps (s₁, σ) (s₁', σ')) : Steps (.seq s₁ s₂, σ) (.seq s₁' s₂, σ') := by
  generalize hc : (s₁, σ) = c at h
  generalize hc' : (s₁', σ') = c' at h
  induction h generalizing s₁ σ s₁' σ' with
  | refl c =>
    subst hc; cases hc'
    exact Steps.refl _
  | step h₁ _ ih =>
    subst hc; subst hc'
    rename_i c₂ _
    obtain ⟨s₂', σ₂⟩ := c₂
    exact Steps.step (Step.seqStep s₂ h₁) (ih rfl rfl)

theorem of_stepsN {n : Nat} {c c' : Config} (h : StepsN n c c') : Steps c c' := by
  induction h with
  | zero => exact Steps.refl _
  | succ h₁ _ ih => exact Steps.step h₁ ih

theorem exists_stepsN {c c' : Config} (h : Steps c c') : ∃ n, StepsN n c c' := by
  induction h with
  | refl => exact ⟨0, StepsN.zero _⟩
  | step h₁ _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, StepsN.succ h₁ hn⟩

end Steps

theorem StepsN.deterministic {n : Nat} {c c₁ c₂ : Config}
    (h₁ : StepsN n c c₁) (h₂ : StepsN n c c₂) : c₁ = c₂ := by
  induction h₁ generalizing c₂ with
  | zero => cases h₂; rfl
  | succ s₁ _ ih =>
    cases h₂ with
    | succ s₂ r₂ =>
      cases Step.deterministic s₁ s₂
      exact ih r₂

theorem StepsN.trans {m n : Nat} {c₁ c₂ c₃ : Config}
    (h₁ : StepsN m c₁ c₂) (h₂ : StepsN n c₂ c₃) : StepsN (m + n) c₁ c₃ := by
  induction h₁ with
  | zero => simpa using h₂
  | succ s _ ih =>
    rw [Nat.succ_add]
    exact StepsN.succ s (ih h₂)

theorem steps_skip_eq {σ : State} {c : Config} (h : Steps (.skip, σ) c) : c = (.skip, σ) := by
  cases h with
  | refl => rfl
  | step h₁ => exact absurd h₁ skip_stuck

theorem Steps.skip_unique {c : Config} {σ₁ σ₂ : State}
    (h₁ : Steps c (.skip, σ₁)) (h₂ : Steps c (.skip, σ₂)) : σ₁ = σ₂ := by
  generalize hd : (Stmt.skip, σ₁) = d at h₁
  induction h₁ generalizing σ₁ σ₂ with
  | refl => cases hd; cases steps_skip_eq h₂; rfl
  | step s₁ _ ih =>
    cases h₂ with
    | refl => cases hd; exact absurd s₁ skip_stuck
    | step s₂ r₂ =>
      cases Step.deterministic s₁ s₂
      exact ih r₂ hd

theorem Terminates.unique {s : Stmt} {σ σ₁ σ₂ : State}
    (h₁ : Terminates s σ σ₁) (h₂ : Terminates s σ σ₂) : σ₁ = σ₂ :=
  Steps.skip_unique h₁ h₂

theorem Diverges.step {c c' : Config} (hd : Diverges c) (hs : Step c c') : Diverges c' := by
  intro n
  obtain ⟨c'', h⟩ := hd (n + 1)
  cases h with
  | succ s r =>
    cases Step.deterministic hs s
    exact ⟨c'', r⟩

theorem Diverges.can_step {c : Config} (hd : Diverges c) : ∃ c', Step c c' := by
  obtain ⟨c', h⟩ := hd 1
  cases h with
  | succ s _ => exact ⟨_, s⟩

theorem Diverges.not_terminates {s : Stmt} {σ σ' : State}
    (hd : Diverges (s, σ)) (ht : Terminates s σ σ') : False := by
  unfold Terminates at ht
  generalize hc : (s, σ) = c at ht hd
  generalize hd' : (Stmt.skip, σ') = d at ht
  clear hc
  induction ht with
  | refl => cases hd'; exact absurd hd.can_step (by rintro ⟨_, h⟩; exact skip_stuck h)
  | step h₁ _ ih => exact ih (hd.step h₁) hd'

theorem Diverges.of_not_terminates {s : Stmt} {σ : State}
    (h : ¬ ∃ σ', Terminates s σ σ') : Diverges (s, σ) := by
  intro n
  induction n with
  | zero => exact ⟨_, StepsN.zero _⟩
  | succ n ih =>
    obtain ⟨⟨s', σ'⟩, hn⟩ := ih
    have hs' : s' ≠ .skip := by
      rintro rfl
      exact h ⟨σ', Steps.of_stepsN hn⟩
    obtain ⟨c'', hstep⟩ := progress s' σ' hs'
    exact ⟨c'', StepsN.trans hn (StepsN.succ hstep (StepsN.zero _))⟩

theorem diverges_iff_not_terminates (s : Stmt) (σ : State) :
    Diverges (s, σ) ↔ ¬ ∃ σ', Terminates s σ σ' :=
  ⟨fun hd ⟨_, ht⟩ => hd.not_terminates ht, Diverges.of_not_terminates⟩

theorem terminates_or_diverges (s : Stmt) (σ : State) :
    (∃ σ', Terminates s σ σ') ∨ Diverges (s, σ) := by
  by_cases h : ∃ σ', Terminates s σ σ'
  · exact Or.inl h
  · exact Or.inr (Diverges.of_not_terminates h)

theorem InfiniteTrace.stepsN {f : Nat → Config} (hf : ∀ n, Step (f n) (f (n + 1))) :
    ∀ n, StepsN n (f 0) (f n) := by
  intro n
  induction n with
  | zero => exact StepsN.zero _
  | succ n ih => exact StepsN.trans ih (StepsN.succ (hf n) (StepsN.zero _))

theorem InfiniteTrace.diverges {c : Config} (h : InfiniteTrace c) : Diverges c := by
  obtain ⟨f, hf0, hf⟩ := h
  intro n
  exact ⟨f n, hf0 ▸ InfiniteTrace.stepsN hf n⟩

theorem StepsN.zero_eq {c c' : Config} (h : StepsN 0 c c') : c = c' := by
  generalize hn : 0 = n at h
  cases h with
  | zero => rfl
  | succ => omega

theorem StepsN.succ_last {n : Nat} {c c'' : Config} (h : StepsN (n + 1) c c'') :
    ∃ c', StepsN n c c' ∧ Step c' c'' := by
  induction n generalizing c with
  | zero =>
    cases h with
    | succ s r => cases StepsN.zero_eq r; exact ⟨_, StepsN.zero _, s⟩
  | succ n ih =>
    cases h with
    | succ s r =>
      obtain ⟨c', hc', hs⟩ := ih r
      exact ⟨c', StepsN.succ s hc', hs⟩

theorem Diverges.infiniteTrace {c : Config} (h : Diverges c) : InfiniteTrace c := by
  classical
  refine ⟨fun n => Classical.choose (h n), ?_, ?_⟩
  · exact (StepsN.zero_eq (Classical.choose_spec (h 0))).symm
  · intro n
    have hn := Classical.choose_spec (h n)
    obtain ⟨c', hc', hstep⟩ := StepsN.succ_last (Classical.choose_spec (h (n + 1)))
    cases StepsN.deterministic hn hc'
    exact hstep

theorem diverges_iff_infiniteTrace (c : Config) : Diverges c ↔ InfiniteTrace c :=
  ⟨Diverges.infiniteTrace, InfiniteTrace.diverges⟩

inductive BigStep : Stmt → State → State → Prop where
  | skip (σ : State) : BigStep .skip σ σ
  | assign (x : String) (e : Expr) (σ : State) :
      BigStep (.assign x e) σ (σ.update x (eval σ e))
  | seq {s₁ s₂ : Stmt} {σ σ' σ'' : State} (h₁ : BigStep s₁ σ σ') (h₂ : BigStep s₂ σ' σ'') :
      BigStep (.seq s₁ s₂) σ σ''
  | iteTrue {e : Expr} {s₁ s₂ : Stmt} {σ σ' : State} (he : eval σ e ≠ 0) (h : BigStep s₁ σ σ') :
      BigStep (.ite e s₁ s₂) σ σ'
  | iteFalse {e : Expr} {s₁ s₂ : Stmt} {σ σ' : State} (he : eval σ e = 0) (h : BigStep s₂ σ σ') :
      BigStep (.ite e s₁ s₂) σ σ'
  | whileFalse {e : Expr} {s : Stmt} {σ : State} (he : eval σ e = 0) : BigStep (.while e s) σ σ
  | whileTrue {e : Expr} {s : Stmt} {σ σ' σ'' : State} (he : eval σ e ≠ 0)
      (hb : BigStep s σ σ') (hw : BigStep (.while e s) σ' σ'') : BigStep (.while e s) σ σ''

theorem BigStep.terminates {s : Stmt} {σ σ' : State} (h : BigStep s σ σ') : Terminates s σ σ' := by
  induction h with
  | skip σ => exact Steps.refl _
  | assign x e σ => exact Steps.single (Step.assign x e σ)
  | seq _ _ ih₁ ih₂ =>
    exact Steps.trans (Steps.seq_congr _ ih₁) (Steps.step (Step.seqSkip _ _) ih₂)
  | iteTrue he _ ih => exact Steps.step (Step.iteTrue _ _ he) ih
  | iteFalse he _ ih => exact Steps.step (Step.iteFalse _ _ he) ih
  | whileFalse he =>
    exact Steps.step (Step.whileUnfold _ _ _) (Steps.single (Step.iteFalse _ _ he))
  | whileTrue he _ _ ihb ihw =>
    exact Steps.step (Step.whileUnfold _ _ _)
      (Steps.step (Step.iteTrue _ _ he)
        (Steps.trans (Steps.seq_congr _ ihb) (Steps.step (Step.seqSkip _ _) ihw)))

theorem BigStep.of_step {s s' : Stmt} {σ σ' σ'' : State}
    (hs : Step (s, σ) (s', σ')) (hb : BigStep s' σ' σ'') : BigStep s σ σ'' := by
  generalize hc : (s, σ) = c at hs
  generalize hc' : (s', σ') = c' at hs
  induction hs generalizing s σ s' σ' σ'' with
  | assign x e σ₀ =>
    cases hc; cases hc'
    cases hb
    exact BigStep.assign x e σ₀
  | seqSkip s₀ σ₀ =>
    cases hc; cases hc'
    exact BigStep.seq (BigStep.skip _) hb
  | seqStep s₂ h ih =>
    cases hc; cases hc'
    cases hb with
    | seq h₁ h₂ => exact BigStep.seq (ih h₁ rfl rfl) h₂
  | iteTrue s₁ s₂ h =>
    cases hc; cases hc'
    exact BigStep.iteTrue h hb
  | iteFalse s₁ s₂ h =>
    cases hc; cases hc'
    exact BigStep.iteFalse h hb
  | whileUnfold e s₀ σ₀ =>
    cases hc; cases hc'
    cases hb with
    | iteTrue he h =>
      cases h with
      | seq h₁ h₂ => exact BigStep.whileTrue he h₁ h₂
    | iteFalse he h =>
      cases h
      exact BigStep.whileFalse he

theorem BigStep.of_terminates {s : Stmt} {σ σ' : State} (h : Terminates s σ σ') :
    BigStep s σ σ' := by
  unfold Terminates at h
  generalize hc : (s, σ) = c at h
  generalize hd : (Stmt.skip, σ') = d at h
  induction h generalizing s σ with
  | refl => cases hc; cases hd; exact BigStep.skip _
  | step h₁ _ ih =>
    cases hc
    rename_i c₂ _
    obtain ⟨s₂, σ₂⟩ := c₂
    exact BigStep.of_step h₁ (ih rfl hd)

theorem bigStep_iff_terminates (s : Stmt) (σ σ' : State) :
    BigStep s σ σ' ↔ Terminates s σ σ' :=
  ⟨BigStep.terminates, BigStep.of_terminates⟩

theorem BigStep.unique {s : Stmt} {σ σ₁ σ₂ : State}
    (h₁ : BigStep s σ σ₁) (h₂ : BigStep s σ σ₂) : σ₁ = σ₂ :=
  Terminates.unique h₁.terminates h₂.terminates

end Liveness
