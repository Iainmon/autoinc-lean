import Autoinc.Partial
import Autoinc.Data.Int.Change

namespace ΔInt
namespace Mul

variable (m : Type → Type)  [MonadStateOf (Int × Int) m]

@[simp] def partial_op [Monad m] : PartialOperator Int Int Int ΔInt ΔInt ΔInt m where
  f x y := modifyGet (fun _ => (x * y, (x, y)))
  δf_1 dx := modifyGet (fun ⟨x, y⟩ => (dx * y, (x + dx, y)))
  δf_2 dy := modifyGet (fun ⟨x, y⟩ => (dy * x, (x, y + dy)))


variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf (Int × Int) m]
open LawfulChangeMonad LawfulMonadStateOf
theorem valid_1 : (partial_op m).valid_1 := by
  intro x y dx hv
  cmsimp

theorem valid_2 : (partial_op m).valid_2 := by
  intro x y dx hv
  cmsimp


theorem correct_1 : (partial_op m).correct_1 := by
  intro a b dx hv ; cmsimp ; grind

theorem correct_2 : (partial_op m).correct_2 := by
  intro a b dx hv ; cmsimp ; grind

def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op m).toOperator

def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

end Mul
end ΔInt
