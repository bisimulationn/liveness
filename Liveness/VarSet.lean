namespace Liveness

abbrev VarSet := List String

namespace VarSet

def union (A B : VarSet) : VarSet := A.foldr List.insert B

def remove (x : String) (A : VarSet) : VarSet := A.filter (fun y => decide (y ≠ x))

def Equiv (A B : VarSet) : Prop := A ⊆ B ∧ B ⊆ A

instance : Union VarSet := ⟨union⟩

@[simp] theorem mem_union {x : String} {A B : VarSet} : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  show x ∈ union A B ↔ _
  induction A with
  | nil => simp [union]
  | cons a A ih =>
    simp only [union, List.foldr_cons, List.mem_insert_iff, List.mem_cons]
    rw [← union, ih]
    constructor
    · rintro (h | h | h) <;> simp [h]
    · rintro ((h | h) | h) <;> simp [h]

@[simp] theorem mem_remove {x y : String} {A : VarSet} : y ∈ remove x A ↔ y ∈ A ∧ y ≠ x := by
  simp [remove]

theorem subset_union_left (A B : VarSet) : A ⊆ A ∪ B := fun _ h => mem_union.2 (Or.inl h)

theorem subset_union_right (A B : VarSet) : B ⊆ A ∪ B := fun _ h => mem_union.2 (Or.inr h)

theorem union_subset {A B C : VarSet} (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C := by
  intro x hx
  rcases mem_union.1 hx with h | h
  · exact hA h
  · exact hB h

theorem union_mono {A A' B B' : VarSet} (hA : A ⊆ A') (hB : B ⊆ B') : A ∪ B ⊆ A' ∪ B' :=
  union_subset (List.Subset.trans hA (subset_union_left _ _))
    (List.Subset.trans hB (subset_union_right _ _))

theorem remove_subset (x : String) (A : VarSet) : remove x A ⊆ A := fun _ h => (mem_remove.1 h).1

theorem remove_mono {A B : VarSet} (x : String) (h : A ⊆ B) : remove x A ⊆ remove x B := by
  intro y hy
  rcases mem_remove.1 hy with ⟨hA, hne⟩
  exact mem_remove.2 ⟨h hA, hne⟩

theorem Equiv.refl (A : VarSet) : Equiv A A := ⟨List.Subset.refl A, List.Subset.refl A⟩

theorem Equiv.symm {A B : VarSet} (h : Equiv A B) : Equiv B A := ⟨h.2, h.1⟩

theorem Equiv.trans {A B C : VarSet} (h₁ : Equiv A B) (h₂ : Equiv B C) : Equiv A C :=
  ⟨List.Subset.trans h₁.1 h₂.1, List.Subset.trans h₂.2 h₁.2⟩

theorem Equiv.mem_iff {A B : VarSet} (h : Equiv A B) {x : String} : x ∈ A ↔ x ∈ B :=
  ⟨fun hx => h.1 hx, fun hx => h.2 hx⟩

theorem Equiv.union {A A' B B' : VarSet} (hA : Equiv A A') (hB : Equiv B B') :
    Equiv (A ∪ B) (A' ∪ B') :=
  ⟨union_mono hA.1 hB.1, union_mono hA.2 hB.2⟩

theorem not_subset_iff {A B : VarSet} : ¬ A ⊆ B ↔ ∃ x, x ∈ A ∧ x ∉ B := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro x hx
    apply Classical.byContradiction
    intro hxB
    exact hne ⟨x, hx, hxB⟩
  · rintro ⟨x, hxA, hxB⟩ hsub
    exact hxB (hsub hxA)

theorem length_filter_le_of_imp {l : List String} {p q : String → Bool}
    (hpq : ∀ a, p a = true → q a = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;>
      first | omega | exact absurd (hpq a hp) (by simp [hq])

theorem length_filter_lt_of_imp {l : List String} {p q : String → Bool}
    (hpq : ∀ a, p a = true → q a = true) (hex : ∃ a, a ∈ l ∧ q a = true ∧ p a = false) :
    (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at hex
  | cons a l ih =>
    obtain ⟨b, hb, hqb, hpb⟩ := hex
    have hle : (l.filter p).length ≤ (l.filter q).length := length_filter_le_of_imp hpq
    rcases List.mem_cons.1 hb with rfl | hbl
    · simp [hpb, hqb]
      omega
    · have := ih ⟨b, hbl, hqb, hpb⟩
      cases hp : p a <;> cases hq : q a <;> simp [hp, hq] <;>
        first | omega | exact absurd (hpq a hp) (by simp [hq])

def deficit (U X : VarSet) : Nat := (U.filter (fun v => !decide (v ∈ X))).length

theorem deficit_lt {U X X' : VarSet} (hXX' : X ⊆ X') (hex : ∃ v, v ∈ U ∧ v ∈ X' ∧ v ∉ X) :
    deficit U X' < deficit U X := by
  unfold deficit
  apply length_filter_lt_of_imp
  · intro a ha
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at ha ⊢
    exact fun h => ha (hXX' h)
  · obtain ⟨v, hU, hX', hX⟩ := hex
    exact ⟨v, hU, by simp [hX], by simp [hX']⟩

end VarSet

end Liveness
