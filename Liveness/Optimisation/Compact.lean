import Liveness.Optimisation.Correctness

namespace Liveness

open VarSet

def seqC : Stmt → Stmt → Stmt
  | .skip, t => t
  | t, .skip => t
  | t₁, t₂ => .seq t₁ t₂

def compact : Stmt → Stmt
  | .seq s₁ s₂ => seqC (compact s₁) (compact s₂)
  | .ite e s₁ s₂ => .ite e (compact s₁) (compact s₂)
  | .while e s => .while e (compact s)
  | s => s

theorem bigStep_seq_iff (t₁ t₂ : Stmt) (σ σ'' : State) :
    BigStep (.seq t₁ t₂) σ σ'' ↔ ∃ σ', BigStep t₁ σ σ' ∧ BigStep t₂ σ' σ'' := by
  constructor
  · intro h
    cases h with
    | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨σ', h₁, h₂⟩
    exact BigStep.seq h₁ h₂

theorem bigStep_skip_seq_iff (t : Stmt) (σ σ'' : State) :
    BigStep t σ σ'' ↔ ∃ σ', BigStep .skip σ σ' ∧ BigStep t σ' σ'' := by
  constructor
  · intro h
    exact ⟨σ, BigStep.skip σ, h⟩
  · rintro ⟨σ', h₁, h₂⟩
    cases h₁
    exact h₂

theorem bigStep_seq_skip_iff (t : Stmt) (σ σ'' : State) :
    BigStep t σ σ'' ↔ ∃ σ', BigStep t σ σ' ∧ BigStep .skip σ' σ'' := by
  constructor
  · intro h
    exact ⟨σ'', h, BigStep.skip σ''⟩
  · rintro ⟨σ', h₁, h₂⟩
    cases h₂
    exact h₁

theorem bigStep_ite_iff (e : Expr) (s₁ s₂ : Stmt) (σ σ' : State) :
    BigStep (.ite e s₁ s₂) σ σ' ↔
      (eval σ e ≠ 0 ∧ BigStep s₁ σ σ') ∨ (eval σ e = 0 ∧ BigStep s₂ σ σ') := by
  constructor
  · intro h
    cases h with
    | iteTrue he h => exact Or.inl ⟨he, h⟩
    | iteFalse he h => exact Or.inr ⟨he, h⟩
  · rintro (⟨he, h⟩ | ⟨he, h⟩)
    · exact BigStep.iteTrue he h
    · exact BigStep.iteFalse he h

theorem bigStep_seqC_iff (t₁ t₂ : Stmt) (σ σ'' : State) :
    BigStep (seqC t₁ t₂) σ σ'' ↔ ∃ σ', BigStep t₁ σ σ' ∧ BigStep t₂ σ' σ'' := by
  cases t₁ <;> cases t₂ <;> simp only [seqC] <;>
    first
    | exact bigStep_skip_seq_iff _ _ _
    | exact bigStep_seq_skip_iff _ _ _
    | exact bigStep_seq_iff _ _ _ _

theorem BigStep.while_mono {s t : Stmt} (hst : ∀ σ σ', BigStep s σ σ' → BigStep t σ σ')
    {e : Expr} {u : Stmt} {σ σ' : State} (h : BigStep u σ σ') (hu : u = .while e s) :
    BigStep (.while e t) σ σ' := by
  induction h with
  | whileFalse he => cases hu; exact BigStep.whileFalse he
  | whileTrue he hb _ _ ihw => cases hu; exact BigStep.whileTrue he (hst _ _ hb) (ihw rfl)
  | _ => cases hu

theorem compact_bigStep_iff (s : Stmt) :
    ∀ σ σ', BigStep (compact s) σ σ' ↔ BigStep s σ σ' := by
  induction s with
  | skip => intro σ σ'; simp only [compact]
  | assign x e => intro σ σ'; simp only [compact]
  | seq s₁ s₂ ih₁ ih₂ =>
    intro σ σ''
    simp only [compact, bigStep_seqC_iff, bigStep_seq_iff, ih₁, ih₂]
  | ite e s₁ s₂ ih₁ ih₂ =>
    intro σ σ'
    simp only [compact, bigStep_ite_iff, ih₁, ih₂]
  | «while» e s ih =>
    intro σ σ'
    simp only [compact]
    exact ⟨fun h => BigStep.while_mono (fun σ σ' => (ih σ σ').1) h rfl,
      fun h => BigStep.while_mono (fun σ σ' => (ih σ σ').2) h rfl⟩

theorem compact_terminates_iff (s : Stmt) (σ σ' : State) :
    Terminates (compact s) σ σ' ↔ Terminates s σ σ' := by
  rw [← bigStep_iff_terminates, ← bigStep_iff_terminates]
  exact compact_bigStep_iff s σ σ'

theorem compact_obsEquiv (L : VarSet) (s : Stmt) : ObsEquiv L s (compact s) :=
  fun σ =>
    ⟨fun σ₁ h => ⟨σ₁, (compact_terminates_iff s σ σ₁).2 h, Agree.refl L σ₁⟩,
      fun σ₂ h => ⟨σ₂, (compact_terminates_iff s σ σ₂).1 h, Agree.refl L σ₂⟩⟩

theorem compact_diverges_iff (s : Stmt) (σ : State) :
    Diverges (compact s, σ) ↔ Diverges (s, σ) :=
  ((compact_obsEquiv [] s).diverges_iff σ).symm

theorem seqC_size_le (t₁ t₂ : Stmt) : (seqC t₁ t₂).size ≤ t₁.size + t₂.size + 1 := by
  cases t₁ <;> cases t₂ <;> simp only [seqC, Stmt.size] <;> omega

theorem compact_size_le (s : Stmt) : (compact s).size ≤ s.size := by
  induction s with
  | skip => exact Nat.le_refl _
  | assign x e => exact Nat.le_refl _
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [compact, Stmt.size]
    have := seqC_size_le (compact s₁) (compact s₂)
    omega
  | ite e s₁ s₂ ih₁ ih₂ =>
    simp only [compact, Stmt.size]
    omega
  | «while» e s ih =>
    simp only [compact, Stmt.size]
    omega

theorem seqC_vars_subset (t₁ t₂ : Stmt) : (seqC t₁ t₂).vars ⊆ t₁.vars ∪ t₂.vars := by
  cases t₁ <;> cases t₂ <;> simp only [seqC, Stmt.vars] <;>
    first
    | exact subset_union_right _ _
    | exact subset_union_left _ _
    | exact List.Subset.refl _

theorem compact_vars_subset (s : Stmt) : (compact s).vars ⊆ s.vars := by
  induction s with
  | skip => exact List.Subset.refl _
  | assign x e => exact List.Subset.refl _
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [compact, Stmt.vars]
    exact List.Subset.trans (seqC_vars_subset _ _) (union_mono ih₁ ih₂)
  | ite e s₁ s₂ ih₁ ih₂ =>
    simp only [compact, Stmt.vars]
    exact union_mono (union_mono (List.Subset.refl _) ih₁) ih₂
  | «while» e s ih =>
    simp only [compact, Stmt.vars]
    exact union_mono (List.Subset.refl _) ih

def optimiseCompact (s : Stmt) (L : VarSet) : Stmt := compact (optimise s L)

theorem optimiseCompact_correct (s : Stmt) (L : VarSet) : ObsEquiv L s (optimiseCompact s L) :=
  (dse_correct s L).trans (compact_obsEquiv L (optimise s L))

theorem optimiseCompact_preserves_divergence (s : Stmt) (L : VarSet) (σ : State) :
    Diverges (s, σ) ↔ Diverges (optimiseCompact s L, σ) :=
  (optimiseCompact_correct s L).diverges_iff σ

theorem optimiseCompact_size_le (s : Stmt) (L : VarSet) : (optimiseCompact s L).size ≤ s.size :=
  Nat.le_trans (compact_size_le _) (optimise_size_le s L)

theorem optimiseCompact_vars_subset (s : Stmt) (L : VarSet) :
    (optimiseCompact s L).vars ⊆ s.vars :=
  List.Subset.trans (compact_vars_subset _) (optimise_vars_subset s L)

end Liveness
