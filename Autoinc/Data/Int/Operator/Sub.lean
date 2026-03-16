import Autoinc.Partial
import Autoinc.Data.Int.Change

namespace ΔInt
namespace Sub
variable (m : Type → Type)

@[simp] def partial_op [Monad m] : PartialOperator Int Int Int ΔInt ΔInt ΔInt m where
  f x y := pure (x - y)
  δf_1 := pure
  δf_2 dy := pure (-dy)


variable [ChangeMonad m] [LawfulChangeMonad m]
open LawfulChangeMonad LawfulMonadStateOf
theorem valid_1 : (partial_op m).valid_1 := by
  simp_all [←bind_pure_comp] ; grind

theorem valid_2 : (partial_op m).valid_2 := by
  simp_all [←bind_pure_comp] ; grind

theorem correct_1 : (partial_op m).correct_1 := by
  simp_all [←bind_pure_comp] ; grind

theorem correct_2 : (partial_op m).correct_2 := by
  simp_all [←bind_pure_comp] ; grind


def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op m).toOperator

def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

end Sub
end ΔInt
