import Autoinc.Operator
import Autoinc.Monad
import Autoinc.Data.Product.Change

structure PartialOperator (α β γ Δα Δβ Δγ : Type) (m : Type → Type) [Monad m] where
  f : α → β → m γ
  δf_1 : Δα → m Δγ
  δf_2 : Δβ → m Δγ

attribute [simp] PartialOperator.f PartialOperator.δf_1 PartialOperator.δf_2

namespace PartialOperator

variable {α β γ Δα Δβ Δγ : Type}
variable [Change α Δα] [Change β Δβ] [Change γ Δγ]

@[simp] def toOperator [Monad m] (op : PartialOperator α β γ Δα Δβ Δγ m) :
  Operator (α × β) γ (ΔProd Δα Δβ) (List Δγ) m where
  f := op.f.uncurry
  Δf | ._1 da => ([·]) <$> op.δf_1 da
     | ._2 db => ([·]) <$> op.δf_2 db
     | ._1_2 da db => ([· , ·]) <$> op.δf_1 da <*> op.δf_2 db

variable {m : Type → Type} [ChangeMonad m]


/- Formal specification of partial operators. -/

variable (op : PartialOperator α β γ Δα Δβ Δγ m)
@[simp] abbrev valid_1' (x : α) (y : β) (dx : Δα) : Prop :=
    x ⊢ dx → op.f x y ⊢ op.δf_1 dx
@[simp] abbrev valid_1 : Prop := ∀ x y dx, op.valid_1' x y dx
@[simp] abbrev valid_2'  (x : α) (y : β) (dy : Δβ) : Prop :=
    y ⊢ dy → op.f x y ⊢ op.δf_2 dy
@[simp] abbrev valid_2 : Prop := ∀ x y dy, op.valid_2' x y dy
@[simp] abbrev correct_1' (x : α) (y : β) (dx : Δα) : Prop :=
    x ⊢ dx → op.f x y ⨁ op.δf_1 dx = op.f (x ⨁ dx) y
@[simp] abbrev correct_1 : Prop := ∀ x y dx, op.correct_1' x y dx
@[simp] abbrev correct_2'  (x : α) (y : β) (dy : Δβ) : Prop :=
    y ⊢ dy → op.f x y ⨁ op.δf_2 dy = op.f x (y ⨁ dy)
@[simp] abbrev correct_2 : Prop := ∀ x y dy, op.correct_2' x y dy

structure spec where
  valid_1 : op.valid_1
  valid_2 : op.valid_2
  correct_1 : op.correct_1
  correct_2 : op.correct_2

variable [LawfulChangeMonad m]

open LawfulChangeMonad in
def toOperatorSpec (p : op.spec) : op.toOperator.spec where
  valid := by
    intro ⟨lhs, rhs⟩ dx hvc
    match dx with
    | ._1 da =>
      obtain h := p.valid_1 lhs rhs da
      simp_all [←bind_pure_comp, seq_eq_bind_map, Change.valid]
    | ._2 db =>
      obtain h := p.valid_2 lhs rhs db
      simp_all [←bind_pure_comp, seq_eq_bind_map, Change.valid]
    | ._1_2 da db =>
      simp_all
      obtain ⟨h₁, h₂⟩ := hvc
      obtain h₃ := p.valid_1 lhs rhs da h₁
      obtain h₄ := p.valid_2 (lhs ⨁ da) rhs db h₂
      simp_all [seq_eq_bind_map, ←(p.correct_1 lhs rhs da h₁), Change.patch, Change.valid]
      exact mprop_conj (mprop_weaken h₃) h₄
  correct := by
    intro ⟨lhs, rhs⟩ dx hvc
    match dx with
    | ._1 da =>
      simp_all
      obtain h₁ := p.correct_1 lhs rhs da hvc
      rw [←h₁]
      simp [←bind_pure_comp, seq_eq_bind_map, Change.patch]
    | ._2 db =>
      simp_all
      obtain h₁ := p.correct_2 lhs rhs db hvc
      rw [←h₁]
      simp [←bind_pure_comp, seq_eq_bind_map, Change.patch]
    | ._1_2 da db =>
      obtain ⟨h_a, h_b⟩ := hvc
      obtain h_1 := p.correct_1 lhs rhs da h_a
      obtain h_2 := p.correct_2 (lhs ⨁ da) rhs db h_b
      simp only [Change.patch, toOperator, Function.uncurry]
      rw [←h_2, ←h_1]
      simp [←bind_pure_comp, seq_eq_bind_map, Change.patch]

end PartialOperator
