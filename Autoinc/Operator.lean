import Autoinc.Change
import Autoinc.Monad

structure Operator (α β Δα Δβ : Type) (m : Type → Type) [Monad m] where
  f : α → m β
  Δf : Δα → m Δβ

namespace Operator

variable (m : Type → Type) [Monad m]
variable {α β Δα Δβ : Type}
variable [Change α Δα]
variable [Change (m β) (m Δβ)]
variable (op : Operator α β Δα Δβ m)
variable (x : α) (dx : Δα)

abbrev valid' := x ⊢ dx → op.f x ⊢ op.Δf dx
abbrev valid := ∀ x dx, op.valid' m x dx
abbrev correct' := x ⊢ dx → op.f (x ⨁ dx) = op.f x ⨁ op.Δf dx
abbrev correct := ∀ x dx, op.correct' m x dx

structure spec where
  valid : op.valid
  correct : op.correct

end Operator

structure MonadicOperator (α β Δα Δβ : Type) (m : Type → Type) [Monad m] where
  f : m α → m β
  Δf : m Δα → m Δβ

namespace Operator
variable (m : Type → Type) [Monad m]
variable {α β Δα Δβ : Type} [Change (m α) (m Δα)] [Change (m β) (m Δβ)]
variable (op : Operator α β Δα Δβ m)
def toM : MonadicOperator α β Δα Δβ m where
  f := (op.f =<< ·)
  Δf := (op.Δf =<< ·)


def mvalid := ∀ (a : m α) (Δa : m Δα),
  a ⊢ Δa → op.f =<< a ⊢ op.Δf =<< Δa

def mcorrect := ∀ (a : m α) (Δa : m Δα),
  a ⊢ Δa → op.f =<< (a ⨁ Δa) = (op.f =<< a) ⨁ (op.Δf =<< Δa)

structure mspec where
  mvalid : op.mvalid
  mcorrect : op.mcorrect

end Operator


namespace OperatorComposition
variable (m : Type → Type) [Monad m]
variable {α β γ Δα Δβ Δγ : Type}
variable (op₁ : Operator α β Δα Δβ m)
variable (op₂ : Operator β γ Δβ Δγ m)
open Operator
def compose : Operator α γ Δα Δγ m where
  f := op₁.f >=> op₂.f
  Δf := op₁.Δf >=> op₂.Δf

variable [Change α Δα] [Change (m β) (m Δβ)] [Change (m γ) (m Δγ)]

theorem compose_valid (spec₁ : op₁.spec) (spec₂ : op₂.mspec) : (compose m op₁ op₂).valid := by
  unfold Operator.valid Operator.valid' compose at *; simp
  intro x dx hvc
  exact (spec₂.mvalid (op₁.f x) (op₁.Δf dx) (spec₁.valid x dx hvc))


theorem compose_correct (spec₁ : op₁.spec) (spec₂ : op₂.mspec) : (compose m op₁ op₂).correct := by
  unfold Operator.correct Operator.correct' compose at *; simp
  intro x dx hvc
  simp only [Bind.kleisliRight, spec₁.correct x dx hvc]
  exact (spec₂.mcorrect (op₁.f x) (op₁.Δf dx) (spec₁.valid x dx hvc))

end OperatorComposition
