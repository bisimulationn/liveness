import Liveness.Analysis.Domain

namespace Liveness

def iterate (U : VarSet) (F : VarSet → VarSet) (hF : Bounded U F) (X : VarSet) (hX : X ⊆ U) :
    VarSet :=
  if _h : F X ⊆ X then X
  else iterate U F hF (X ∪ F X) (VarSet.union_subset hX (hF X hX))
termination_by VarSet.deficit U X
decreasing_by
  apply VarSet.deficit_lt (VarSet.subset_union_left _ _)
  obtain ⟨v, hvF, hvX⟩ := VarSet.not_subset_iff.1 _h
  exact ⟨v, hF X hX hvF, VarSet.mem_union.2 (Or.inr hvF), hvX⟩

def lfp (U : VarSet) (F : VarSet → VarSet) (hF : Bounded U F) : VarSet :=
  iterate U F hF [] (List.nil_subset U)

section Iterate

variable {U : VarSet} {F : VarSet → VarSet} {hF : Bounded U F}

theorem iterate_of_postfixed {X : VarSet} (hX : X ⊆ U) (h : PostFixed F X) :
    iterate U F hF X hX = X := by
  have h' : F X ⊆ X := h
  rw [iterate]; simp [h']

theorem iterate_of_not_postfixed {X : VarSet} (hX : X ⊆ U) (h : ¬ PostFixed F X) :
    iterate U F hF X hX = iterate U F hF (X ∪ F X) (VarSet.union_subset hX (hF X hX)) := by
  have h' : ¬ F X ⊆ X := h
  rw [iterate]; simp [h']

theorem iterate_postfixed (X : VarSet) (hX : X ⊆ U) : PostFixed F (iterate U F hF X hX) := by
  induction X, hX using iterate.induct U F hF with
  | case1 X hX h => rw [iterate_of_postfixed hX h]; exact h
  | case2 X hX h ih => rw [iterate_of_not_postfixed hX h]; exact ih

theorem subset_iterate (X : VarSet) (hX : X ⊆ U) : X ⊆ iterate U F hF X hX := by
  induction X, hX using iterate.induct U F hF with
  | case1 X hX h => rw [iterate_of_postfixed hX h]; exact List.Subset.refl X
  | case2 X hX h ih =>
    rw [iterate_of_not_postfixed hX h]
    exact List.Subset.trans (VarSet.subset_union_left _ _) ih

theorem iterate_subset_universe (X : VarSet) (hX : X ⊆ U) : iterate U F hF X hX ⊆ U := by
  induction X, hX using iterate.induct U F hF with
  | case1 X hX h => rw [iterate_of_postfixed hX h]; exact hX
  | case2 X hX h ih => rw [iterate_of_not_postfixed hX h]; exact ih

theorem iterate_least (hm : Monotone F) (X : VarSet) (hX : X ⊆ U)
    (hXY : ∀ Y, PostFixed F Y → X ⊆ Y) : ∀ Y, PostFixed F Y → iterate U F hF X hX ⊆ Y := by
  induction X, hX using iterate.induct U F hF with
  | case1 X hX h => rw [iterate_of_postfixed hX h]; exact hXY
  | case2 X hX h ih =>
    rw [iterate_of_not_postfixed hX h]
    apply ih
    intro Y hY
    exact VarSet.union_subset (hXY Y hY) (List.Subset.trans (hm _ _ (hXY Y hY)) hY)

end Iterate

section Lfp

variable {U : VarSet} {F : VarSet → VarSet} (hF : Bounded U F)

theorem lfp_postfixed : PostFixed F (lfp U F hF) :=
  iterate_postfixed [] (List.nil_subset U)

theorem lfp_subset_universe : lfp U F hF ⊆ U :=
  iterate_subset_universe [] (List.nil_subset U)

theorem lfp_least (hm : Monotone F) {Y : VarSet} (hY : PostFixed F Y) : lfp U F hF ⊆ Y :=
  iterate_least hm [] (List.nil_subset U) (fun Y _ => List.nil_subset Y) Y hY

theorem lfp_prefixed (hm : Monotone F) : lfp U F hF ⊆ F (lfp U F hF) :=
  lfp_least hF hm (hm _ _ (lfp_postfixed hF))

theorem lfp_fixed (hm : Monotone F) : VarSet.Equiv (F (lfp U F hF)) (lfp U F hF) :=
  ⟨lfp_postfixed hF, lfp_prefixed hF hm⟩

theorem lfp_mono {U' : VarSet} {F' : VarSet → VarSet} (hF' : Bounded U' F')
    (hm : Monotone F) (hle : ∀ X, F X ⊆ F' X) : lfp U F hF ⊆ lfp U' F' hF' :=
  lfp_least hF hm (List.Subset.trans (hle _) (lfp_postfixed hF'))

end Lfp

end Liveness
