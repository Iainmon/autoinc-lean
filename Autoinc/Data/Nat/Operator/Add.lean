import Autoinc.Partial
import Autoinc.Data.Nat.Change

namespace ΔNat
namespace Add
variable (m : Type → Type)

@[simp] def partial_op [Monad m] : PartialOperator Nat Nat Nat ΔNat ΔNat ΔNat m where
  f a b := pure (a + b)
  δf_1 := pure
  δf_2 := pure


variable [ChangeMonad m] [LawfulChangeMonad m]

theorem valid_1 : (partial_op m).valid_1 := by
  intro x y dx h ; cases dx <;> simp_all ; grind

theorem valid_2 : (partial_op m).valid_2 := by
  intro x y dy h ; cases dy <;> simp_all ; grind

theorem correct_1 : (partial_op m).correct_1 := by
  intro x y dx h ; simp_all ; congr ; grind [cases ΔNat]

theorem correct_2 : (partial_op m).correct_2 := by
  intros x y dy h ; cases dy <;> simp_all <;> grind


def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m

def op [Monad m] := (partial_op m).toOperator
def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

end Add
end ΔNat
