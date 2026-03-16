import Autoinc.Change

/-- change representation for Option -/
inductive ΔOption (α Δα : Type) : Type where
  | noc : ΔOption α Δα
  | to_none : ΔOption α Δα
  | to_some : α → ΔOption α Δα
  | change_some : Δα → ΔOption α Δα
  deriving Repr, BEq

instance [ToString α] [ToString Δα] : ToString (ΔOption α Δα) where
  toString d := match d with
    | .noc => s!"noc"
    | .to_none => s!"to_none"
    | .to_some t => s!"to_some {t}"
    | .change_some dt => s!"change_some {dt}"

instance : Inhabited (ΔOption α Δα) where
  default := .noc

/-- change class for Option -/
instance OptionChange (α : Type) (Δα : Type) [Change α Δα]
  : Change (Option α) (ΔOption α Δα) where
  patch o d := match d with
  | ΔOption.noc => o
  | ΔOption.to_none => none
  | ΔOption.to_some t => some t
  | ΔOption.change_some dt => match o with
    | none => none
    | some t => some (Change.patch t dt)
  valid o d := match d with
  | ΔOption.noc => True
  | ΔOption.to_none => o.isSome
  | ΔOption.to_some _ => o.isNone
  | ΔOption.change_some c => match o with
    | none => False
    | some v => Change.valid v c

@[simp] theorem OptionChange.valid_noc {α : Type} {Δα : Type} [Change α Δα]
  {o : Option α} :
  o ⊢ (ΔOption.noc : ΔOption α Δα) := by simp [Change.valid]
@[simp] theorem OptionChange.valid_to_none {α : Type} {Δα : Type} [Change α Δα]
  {a : α} :
  some a ⊢ (ΔOption.to_none : ΔOption α Δα) := by simp [Change.valid]
@[simp] theorem OptionChange.valid_to_some {α : Type} {Δα : Type} [Change α Δα]
  {a : α} :
  (none : Option α) ⊢ (ΔOption.to_some a : ΔOption α Δα) := by simp [Change.valid]
@[simp] theorem OptionChange.valid_change_some {α : Type} {Δα : Type} [Change α Δα]
  {a : α} {Δa : Δα} (val_a : a ⊢ Δa) :
  some a ⊢ (ΔOption.change_some Δa : ΔOption α Δα) := by simp [Change.valid]; exact val_a

@[simp] theorem OptionChange.patch_noc {α : Type} {Δα : Type} [Change α Δα]
  {o : Option α} :
  o ⨁ (ΔOption.noc : ΔOption α Δα) = o := by simp [Change.patch]
@[simp] theorem OptionChange.patch_to_none {α : Type} {Δα : Type} [Change α Δα]
  {a : α} :
  (some a : Option α) ⨁ (ΔOption.to_none : ΔOption α Δα) = none := by simp [Change.patch]
@[simp] theorem OptionChange.patch_to_some {α : Type} {Δα : Type} [Change α Δα]
  {a : α} :
  (none : Option α) ⨁ (ΔOption.to_some a : ΔOption α Δα) = some a := by simp [Change.patch]
@[simp] theorem OptionChange.patch_change_some {α : Type} {Δα : Type} [Change α Δα]
  {a : α} {Δa : Δα} :
  (some a : Option α) ⨁ (ΔOption.change_some Δa : ΔOption α Δα) = some (a ⨁ Δa) := by simp [Change.patch]

instance OptionDifference (α : Type) (Δα : Type) [Change α Δα] [Difference α Δα]
  : Difference (Option α) (ΔOption α Δα) where
  diff new old := match new, old with
  | none, none => ΔOption.noc
  | none, some _ => ΔOption.to_none
  | some t, none => ΔOption.to_some t
  | some t, some v => ΔOption.change_some (Difference.diff t v)
  diff_valid new old := by cases old <;> cases new <;> simp_all; apply Difference.diff_valid
  diff_correct new old := by cases old <;> cases new <;> simp_all; apply Difference.diff_correct
