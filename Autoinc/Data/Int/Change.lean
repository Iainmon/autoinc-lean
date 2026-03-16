import Autoinc.Change

abbrev ΔInt := Int

instance IntChange : Change Int ΔInt where
  patch k Δk := k + Δk
  valid _ _ := True

@[simp, grind] theorem IntChange.valid' {k : Int} {Δk : ΔInt} : k ⊢ Δk := by simp [Change.valid]
@[simp, grind] theorem IntChange.patch' (k : Int) (Δk : ΔInt) : k ⨁ Δk = k + Δk := rfl

instance IntDifference : Difference Int ΔInt where
  diff x y := x - y
  diff_valid x y := by simp
  diff_correct x y := by simp; omega

