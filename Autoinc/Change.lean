/-- change class -/
class Change (α Δα : Type) where
  /-- patch function to apply a change to a value -/
  patch : α → Δα → α
  /-- validity predicate to check if a change is valid for a given value -/
  valid : α → Δα → Prop

infixl:60 " ⨁ " => Change.patch
infixl:40 " ⊢ " => Change.valid

@[grind] class Difference (α Δα : Type) [Change α Δα] where
  /-- (diff new old) function to compute the change between two values -/
  diff : α → α → Δα
  diff_valid : ∀ old new, old ⊢ diff new old
  diff_correct : ∀ old new, old ⨁ diff new old = new

class Noc (Δα : Type) where
  noc : Δα

def nocThe (Δα : Type) [Noc Δα] : Δα := Noc.noc

class LawfulNoChange (α Δα : Type) [Noc Δα] [Change α Δα] where
  valid_noc : ∀ (t : α), t ⊢ nocThe Δα
  correct_noc : ∀ (t : α), t ⨁ nocThe Δα = t


/-- new ⊖ old -/
infixl: 70 " ⊖ " => Difference.diff

@[simp] def valid_all {T ΔT : Type} [Change T ΔT] (t : T) (ds : List ΔT) : Prop := match ds, t with
| [], _ => True
| d :: ds, t => t ⊢ d ∧ valid_all (t ⨁ d) ds

section
/-
Change structure which has an extra boolean function that determines whether a change descriptor does nothing.
-/
class ChangeNoc (α Δα : Type) extends Change α Δα where
  is_noc : α → Δα → Prop
  valid_noc : ∀ (t : α) Δt, is_noc t Δt → t ⊢ Δt
  correct_noc : ∀ (t : α) Δt, is_noc t Δt → t ⨁ Δt = t
end


section
/-- A change structure that each change decriptor has an inverse -/
class ChangeInversion (α Δα : Type) extends Change α Δα where
  invert : Δα → Δα
  valid_invert : ∀ (t : α) Δt, t ⊢ Δt → t ⨁ Δt ⊢ invert Δt
  correct_invert : ∀ (t : α) Δt, t ⊢ Δt → t ⨁ Δt ⨁ (invert Δt) = t
end


section
/-
Lifting a change structure to handle sequential (list of) changes.
-/

variable {α Δα : Type} [Change α Δα]
/-- change structure for sequences of changes -/
instance ChangeSeq : Change α (List Δα) where
  patch t ds := ds.foldl (· ⨁ ·) t
  valid t ds := go t ds where
    go : α → List Δα → Prop
      | _, [] => True
      | t, d :: ds => t ⊢ d ∧ go (t ⨁ d) ds

attribute [simp, grind] ChangeSeq.go

variable (t : α) (ds₁ ds₂ : List Δα)

@[simp, grind] theorem ChangeSeq.patch_seq_nil :
  t ⨁ ([] : List Δα) = t := by simp [Change.patch]

@[simp, grind] theorem ChangeSeq.patch_seq_cons :
  t ⨁ (d :: ds₁) = (t ⨁ d) ⨁ ds₁ := by simp [Change.patch]

@[simp, grind] theorem ChangeSeq.patch_seq_append :
  t ⨁ ds₁ ⨁ ds₂ = t ⨁ (ds₁ ++ ds₂) := by simp [Change.patch]


@[simp, grind] theorem ChangeSeq.valid_seq_nil :
  t ⊢ ([] : List Δα) := by simp [Change.valid]

@[simp, grind] theorem ChangeSeq.valid_seq_cons :
  (t ⊢ d) ∧ (t ⨁ d ⊢ ds₁) → t ⊢ (d :: ds₁) := by simp [Change.valid]
@[grind] theorem ChangeSeq.valid_seq_cons_elim :
  t ⊢ (d :: ds₁) → (t ⊢ d) ∧ (t ⨁ d ⊢ ds₁) := by simp [Change.valid]

@[simp, grind] theorem ChangeSeq.valid_seq_append_intro :
  t ⊢ ds₁ ++ ds₂ → t ⨁ ds₁ ⊢ ds₂ := by
  induction ds₁ generalizing t ds₂ <;> simp_all [Change.valid]
@[grind] theorem ChangeSeq.valid_seq_append_elim :
  t ⊢ ds₁ → t ⨁ ds₁ ⊢ ds₂ → t ⊢ ds₁ ++ ds₂ := by
  induction ds₁ generalizing t ds₂ <;> simp_all [Change.valid]


end


section
/-
Lift a change structure to handle optional changes.
-/
variable {α Δα : Type} [Change α Δα]

instance ChangeOption : Change α (Option Δα) where
  patch t d := Option.elim d t (t ⨁ ·)
  valid t d := Option.elim d True (t ⊢ ·)

end


section
/-
Lift change structures to work on product types
-/

variable {α β Δα Δβ : Type} [Change α Δα] [Change β Δβ]
instance ChangePair : Change (α × β) (Δα × Δβ) where
  patch | (a, b), (Δa, Δb) => (a ⨁ Δa, b ⨁ Δb)
  valid | (a, b), (Δa, Δb) => a ⊢ Δa /\ b ⊢ Δb
end
