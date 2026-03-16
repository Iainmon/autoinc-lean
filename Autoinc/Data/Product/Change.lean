import Autoinc.Change

/-- change representation for Product -/
inductive ΔProd (Δα Δβ : Type) : Type where
  | _1 : Δα → ΔProd Δα Δβ
  | _2 : Δβ → ΔProd Δα Δβ
  | _1_2 : Δα → Δβ → ΔProd Δα Δβ
  deriving Repr

instance [ToString Δα] [ToString Δβ] : ToString (ΔProd Δα Δβ) where
  toString | ._1 a => "ΔProd._1 " ++ toString a
           | ._2 b => "ΔProd._2 " ++ toString b
           | ._1_2 a b => "ΔProd._1_2 (" ++ toString a ++ ", " ++ toString b ++ ")"

@[simp] def ProdChange.valid  [Change α Δα] [Change β Δβ] (p : α × β)  : ΔProd Δα Δβ → Prop
| ΔProd._1 da => p.1 ⊢ da
| ΔProd._2 db => p.2 ⊢ db
| ΔProd._1_2 da db => p.1 ⊢ da ∧ p.2 ⊢ db

/-- change class for Product -/
instance ProdChange (α β : Type) (Δα Δβ : Type) [Change α Δα] [Change β Δβ]
  : Change (α × β) (ΔProd Δα Δβ) where
  patch p d := match d with
  | ΔProd._1 da => match p with
    | (a, b) => (a ⨁ da, b)
  | ΔProd._2 db => match p with
    | (a, b) => (a, b ⨁ db)
  | ΔProd._1_2 da db => match p with
    | (a, b) => (a ⨁ da, b ⨁ db)
  valid := ProdChange.valid

@[simp, grind] theorem ProdChange.valid_1 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) :
  p.1 ⊢ da ↔ p ⊢ (ΔProd._1 da : ΔProd Δα Δβ) := by simp [Change.valid]
@[grind] theorem ProdChange.valid_1_elim {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) :
  p ⊢ (ΔProd._1 da : ΔProd Δα Δβ) → p.1 ⊢ da := by simp [Change.valid]
@[simp, grind] theorem ProdChange.valid_2 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (db : Δβ) :
  p.2 ⊢ db ↔ p ⊢ (ΔProd._2 db : ΔProd Δα Δβ) := by simp [Change.valid]
@[grind] theorem ProdChange.valid_2_elim {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (db : Δβ) :
  p ⊢ (ΔProd._2 db : ΔProd Δα Δβ) → p.2 ⊢ db := by simp [Change.valid]
@[grind] theorem ProdChange.valid_1_2 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) (db : Δβ) :
  (p.1 ⊢ da ∧ p.2 ⊢ db) ↔ p ⊢ (ΔProd._1_2 da db : ΔProd Δα Δβ) := by simp [Change.valid]
@[grind] theorem ProdChange.valid_1_2_elim {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) (db : Δβ) :
  p ⊢ (ΔProd._1_2 da db : ΔProd Δα Δβ) → (p.1 ⊢ da ∧ p.2 ⊢ db) := by simp [Change.valid]
@[simp, grind] theorem ProdChange.patch_1 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) :
  p ⨁ (ΔProd._1 da : ΔProd Δα Δβ) = (p.1 ⨁ da, p.2) := by simp [Change.patch]
@[simp, grind] theorem ProdChange.patch_2 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (db : Δβ) :
  p ⨁ (ΔProd._2 db : ΔProd Δα Δβ) = (p.1, p.2 ⨁ db) := by simp [Change.patch]
@[simp, grind] theorem ProdChange.patch_1_2 {α β : Type} {Δα Δβ : Type} [Change α Δα] [Change β Δβ]
  (p : α × β) (da : Δα) (db : Δβ) :
  p ⨁ (ΔProd._1_2 da db : ΔProd Δα Δβ) = (p.1 ⨁ da, p.2 ⨁ db) := by simp [Change.patch]

@[simp] def ProductChange.invert {α β : Type} {Δα Δβ : Type}
  [C₁ : ChangeInversion α Δα] [C₂ : ChangeInversion β Δβ] :
    ΔProd Δα Δβ → ΔProd Δα Δβ
    | ΔProd._1 Δx => ΔProd._1 (C₁.invert Δx)
    | ΔProd._2 Δx => ΔProd._2 (C₂.invert Δx)
    | ΔProd._1_2 Δx Δy => ΔProd._1_2 (C₁.invert Δx) (C₂.invert Δy)

instance (α β : Type) (Δα Δβ : Type)
  [C₁ : ChangeInversion α Δα] [C₂ : ChangeInversion β Δβ] : ChangeInversion (α × β) (ΔProd Δα Δβ) where
  invert := ProductChange.invert
  valid_invert : ∀ (t : α × β) (Δt : ΔProd Δα Δβ),
    t ⊢ Δt → t ⨁ Δt ⊢ ProductChange.invert Δt := by
    simp ; intros ; split at * <;> simp at *
    · apply ChangeInversion.valid_invert; assumption
    · apply ChangeInversion.valid_invert; assumption
    · apply And.intro <;>
      apply ChangeInversion.valid_invert <;> simp_all [← ProdChange.valid_1_2]
  correct_invert : ∀ (t : α × β) (Δt : ΔProd Δα Δβ),
    t ⊢ Δt → t ⨁ Δt ⨁ ProductChange.invert Δt = t := by
    simp ; intros ; split at * <;> simp at *
    · rw [ChangeInversion.correct_invert] <;> assumption
    · rw [ChangeInversion.correct_invert] <;> assumption
    · apply And.intro <;> rw [ChangeInversion.correct_invert] <;> simp_all [← ProdChange.valid_1_2]

namespace ΔProd
variable {Δα Δβ Δγ : Type}
def first_1  (dx : Δα) : ΔProd (ΔProd Δα Δβ) Δγ := ΔProd._1 (ΔProd._1 dx)
def first_2  (dx : Δβ) : ΔProd (ΔProd Δα Δβ) Δγ := ΔProd._1 (ΔProd._2 dx)

end ΔProd
