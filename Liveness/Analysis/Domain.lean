import Liveness.VarSet

namespace Liveness

def Monotone (F : VarSet → VarSet) : Prop := ∀ A B, A ⊆ B → F A ⊆ F B

def Bounded (U : VarSet) (F : VarSet → VarSet) : Prop := ∀ X, X ⊆ U → F X ⊆ U

def PostFixed (F : VarSet → VarSet) (X : VarSet) : Prop := F X ⊆ X

namespace VarSet

theorem subset_union_of_left {A B C : VarSet} (h : A ⊆ B) : A ⊆ B ∪ C :=
  List.Subset.trans h (subset_union_left B C)

theorem subset_union_of_right {A B C : VarSet} (h : A ⊆ C) : A ⊆ B ∪ C :=
  List.Subset.trans h (subset_union_right B C)

theorem union_assoc_subset (A B C : VarSet) : A ∪ B ∪ C ⊆ A ∪ (B ∪ C) := by
  intro x hx
  simp only [mem_union] at hx ⊢
  rcases hx with (h | h) | h <;> simp [h]

theorem union_comm_subset (A B : VarSet) : A ∪ B ⊆ B ∪ A := by
  intro x hx
  simp only [mem_union] at hx ⊢
  rcases hx with h | h <;> simp [h]

end VarSet

end Liveness
