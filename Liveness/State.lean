namespace Liveness

abbrev State := String → Int

namespace State

def update (σ : State) (x : String) (v : Int) : State :=
  fun y => if y = x then v else σ y

@[simp] theorem update_same (σ : State) (x : String) (v : Int) :
    update σ x v x = v := by
  simp [update]

@[simp] theorem update_other (σ : State) {x y : String} (v : Int) (h : y ≠ x) :
    update σ x v y = σ y := by
  simp [update, h]

theorem update_apply (σ : State) (x y : String) (v : Int) :
    update σ x v y = if y = x then v else σ y := rfl

end State

end Liveness
