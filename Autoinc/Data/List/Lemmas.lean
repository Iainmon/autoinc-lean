import Autoinc.Change
import Autoinc.Data.List.Change



set_option linter.unnecessarySimpa false

/-- If you `drop` some of what you `take`, you get the rest. -/
theorem List.drop_take_add (a b : Nat) (xs : List α) :
  List.drop a (List.take (a + b) xs) = List.take b (List.drop a xs) := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
      cases a <;> simpa [Nat.succ_add] using ih _

/-- If you `drop` at least as much as you `take`, you get `[]`. -/
@[simp, grind] theorem List.drop_ge_take (a b : Nat) (xs : List α) (h : b ≤ a) :
  List.drop a (List.take b xs) = [] := by
    simp_all only [List.drop_eq_nil_iff, List.length_take]; grind

attribute [grind] List.take_of_length_le List.take_take


@[simp] theorem Nat.sub_eq_zero_of_lt {a b : Nat} (h : a > b) : (b - a) = 0 := by grind

@[simp] theorem Nat.add_sub_cancel₁ {a b : Nat} : a + b + c - a = b + c := by grind
@[simp] theorem Nat.add_sub_cancel₂ {a b : Nat} (h : a ≤ c) : a + b + (c - a) = b + c := by grind

@[simp] theorem List.drop_take_drop : List.drop a (List.take b (List.drop c x)) = List.drop (c + a) (List.take (c + b) x) := by
  rw [List.take_drop, List.drop_drop]

@[simp, grind] theorem List.drop_append_eq {n i k} {x : List α} (h : (i + k - min n x.length) = 0)  :
  List.drop (i + k) (List.take (k + n) x) = List.drop (i + k) (List.take n x) ++ List.drop n (List.take (k + n) x) := by
  rw [Nat.add_comm k n, List.take_add, List.drop_append]
  simp; rw [h]; simp; grind
