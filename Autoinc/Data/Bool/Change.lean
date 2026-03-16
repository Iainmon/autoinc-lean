import Autoinc.Change

section
variable {t : Bool}
/-- change representation for Bool -/
inductive ΔBool : Type where
  | noc : ΔBool
  | flip : ΔBool
deriving Repr, BEq

instance : ToString ΔBool where
  toString | .noc => "noc"
           | .flip => "flip"


/-- change class for Bool -/
instance BoolChange : Change Bool ΔBool where
  patch b d := match d with
  | ΔBool.noc => b
  | ΔBool.flip => not b
  valid _ _ := True

@[simp] theorem Bool.valid (b : Bool) (Δb : ΔBool) : b ⊢ Δb := by simp [Change.valid]

@[simp] theorem Bool.patch_noc (k : Bool) : Change.patch k ΔBool.noc = k := rfl
@[simp] theorem Bool.patch_flip (k : Bool) : Change.patch k ΔBool.flip = not k := rfl

instance : Mul ΔBool where
  mul Δx Δy := match Δx, Δy with
      | ΔBool.noc, Δy => Δy
      | Δx, ΔBool.noc => Δx
      | ΔBool.flip, ΔBool.flip => ΔBool.noc

instance : One ΔBool where
  one := ΔBool.noc



@[simp] def is_noc Δx := match Δx with
    | ΔBool.noc => True
    | _ => False

instance : ChangeNoc Bool ΔBool where
  is_noc x Δx := is_noc Δx
  valid_noc : ∀ t Δt, (is_noc Δt) → t ⊢ Δt := by
    intros t Δt h ; cases t <;> cases Δt <;> simp
  correct_noc : ∀ t Δt, is_noc Δt → t ⨁ Δt = t := by
    intros t Δt h ; cases t <;> cases Δt <;> simp at *


/-- change inversion for bool -/
instance : ChangeInversion Bool ΔBool where
  invert Δx := Δx
  valid_invert : ∀ (t : Bool) (Δt : ΔBool), t ⊢ Δt → t ⨁ Δt ⊢ Δt := by
    intro t Δt h ; cases t <;> cases Δt <;> simp at *
  correct_invert : ∀ (t : Bool) (Δt : ΔBool), t ⊢ Δt → t ⨁ Δt ⨁ Δt = t := by
    intro t Δt h ; cases t <;> cases Δt <;> simp at *


@[simp] def boolDiff (new old : Bool) : ΔBool :=
    match new, old with
    | false, true => .flip
    | true, false => .flip
    | _, _ => .noc

instance : Difference Bool ΔBool where
  diff := boolDiff
  diff_valid : ∀ (old new : Bool), old ⊢ boolDiff new old := by simp_all
  diff_correct : ∀ (old new : Bool), old ⨁ boolDiff new old = new := by simp_all

@[simp] theorem Bool.diff (k1 k2 : Bool) : Difference.diff k1 k2 = boolDiff k1 k2 := rfl
