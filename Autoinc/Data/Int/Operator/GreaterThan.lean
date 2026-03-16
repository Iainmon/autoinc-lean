import Autoinc.Partial
import Autoinc.Data.Int.Change
import Autoinc.Data.Bool.Change
import Autoinc.Data.Product.Change
import AssertCmd

namespace ΔInt
namespace GreaterThan

variable (m : Type → Type) [MonadStateOf Int m]

@[simp] def flip? (d1 d2 : Int) : ΔBool × Int :=
  if (d1 > 0 : Bool) != (d2 > 0 : Bool) then (ΔBool.flip, d2) else (ΔBool.noc, d2)

@[simp] def partial_op [Monad m] : PartialOperator Int Int Bool ΔInt ΔInt ΔBool m where
  f a b := modifyGet (fun _ => (if a > b then true else false, (a - b)))
  δf_1 dx := modifyGet (fun d => flip? d (d + dx))
  δf_2 dy := modifyGet (fun d => flip? d (d - dy))

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf Int m]
open LawfulChangeMonad LawfulMonadStateOf

theorem valid_1 : (partial_op m).valid_1 := by
  intro x y dx hv
  cmsimp

theorem valid_2 : (partial_op m).valid_2 := by
  intro x y dx hv
  cmsimp

theorem correct_1 : (partial_op m).correct_1 := by
  intro a b dx hv ; cmsimp ; simp_all [Change.patch] ; grind

theorem correct_2 : (partial_op m).correct_2 := by
  intro a b dx hv ; cmsimp ; simp_all [Change.patch] ; grind

def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op m).toOperator

def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)


end GreaterThan
end ΔInt
