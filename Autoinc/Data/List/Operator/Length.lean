import Autoinc.Operator
import Autoinc.Monad
import Autoinc.Data.List.Change


namespace ΔList
namespace Length
variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)
@[simp] def op [Monad m] : Operator (List α) Nat (ΔList α Δα) ΔNat m where
  f x := pure x.length
  Δf | ins _ l => pure <| .inc l.length
     | del _ n => pure <| .dec n
     | upd _ _ => pure <| .inc 0
variable [ChangeMonad m] [LawfulChangeMonad m]
attribute [simp] LawfulChangeMonad.mprop_pure
theorem op_valid  : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx hvc
  cases dx <;> simp_all ; grind

theorem op_correct : (op (α:=α) (Δα:=Δα) m).correct := by
  intro x dx hvc
  cases dx <;> simp_all <;> congr 1 <;> grind

def spec : (op (α:=α) (Δα:=Δα) m).spec where
  valid := op_valid m
  correct := op_correct m

end Length
end ΔList
