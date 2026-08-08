import Liveness.Semantics

namespace Liveness

def stepFn : Stmt → State → Option Config
  | .skip, _ => none
  | .assign x e, σ => some (.skip, σ.update x (eval σ e))
  | .seq s₁ s₂, σ =>
    if s₁ = .skip then some (s₂, σ)
    else
      match stepFn s₁ σ with
      | some (s₁', σ') => some (.seq s₁' s₂, σ')
      | none => none
  | .ite e s₁ s₂, σ => if eval σ e = 0 then some (s₂, σ) else some (s₁, σ)
  | .while e s, σ => some (.ite e (.seq s (.while e s)) .skip, σ)

theorem stepFn_sound {s : Stmt} {σ : State} {c' : Config} (h : stepFn s σ = some c') :
    Step (s, σ) c' := by
  induction s generalizing σ c' with
  | skip => simp [stepFn] at h
  | assign x e => simp only [stepFn, Option.some.injEq] at h; subst h; exact Step.assign x e σ
  | seq s₁ s₂ ih₁ _ =>
    simp only [stepFn] at h
    split at h
    · rename_i hs
      subst hs
      cases h
      exact Step.seqSkip s₂ σ
    · split at h
      · rename_i s₁' σ' hs
        cases h
        exact Step.seqStep s₂ (ih₁ hs)
      · cases h
  | ite e s₁ s₂ =>
    simp only [stepFn] at h
    split at h
    · rename_i he; cases h; exact Step.iteFalse s₁ s₂ he
    · rename_i he; cases h; exact Step.iteTrue s₁ s₂ he
  | «while» e s =>
    simp only [stepFn, Option.some.injEq] at h; subst h; exact Step.whileUnfold e s σ

theorem stepFn_complete {s : Stmt} {σ : State} {c' : Config} (h : Step (s, σ) c') :
    stepFn s σ = some c' := by
  generalize hc : (s, σ) = c at h
  induction h generalizing s σ with
  | assign x e σ₀ => cases hc; rfl
  | seqSkip s₀ σ₀ => cases hc; simp [stepFn]
  | seqStep s₂ h ih =>
    rename_i s₁ s₁' σ₁ σ₁'
    cases hc
    have hne : s₁ ≠ Stmt.skip := by
      rintro rfl
      exact skip_stuck h
    simp [stepFn, hne, ih rfl]
  | iteTrue s₁ s₂ h => cases hc; simp [stepFn, h]
  | iteFalse s₁ s₂ h => cases hc; simp [stepFn, h]
  | whileUnfold e s₀ σ₀ => cases hc; rfl

theorem stepFn_iff (s : Stmt) (σ : State) (c' : Config) : stepFn s σ = some c' ↔ Step (s, σ) c' :=
  ⟨stepFn_sound, stepFn_complete⟩

inductive Outcome where
  | finished : State → Outcome
  | outOfFuel : Config → Outcome

def run : Nat → Stmt → State → Outcome
  | _, .skip, σ => .finished σ
  | 0, s, σ => .outOfFuel (s, σ)
  | n + 1, s, σ =>
    match stepFn s σ with
    | some (s', σ') => run n s' σ'
    | none => .outOfFuel (s, σ)

theorem run_finished_sound {n : Nat} {s : Stmt} {σ σ' : State} (h : run n s σ = .finished σ') :
    Terminates s σ σ' := by
  induction n generalizing s σ with
  | zero =>
    cases s with
    | skip => simp only [run, Outcome.finished.injEq] at h; subst h; exact Steps.refl _
    | _ => simp [run] at h
  | succ n ih =>
    cases s with
    | skip => simp only [run, Outcome.finished.injEq] at h; subst h; exact Steps.refl _
    | _ =>
      simp only [run] at h
      split at h
      · rename_i s'' σ'' hc
        exact Steps.step (stepFn_sound hc) (ih h)
      · cases h

end Liveness
