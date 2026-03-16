import Autoinc.Partial
import Autoinc.Data.List.Change


namespace ΔList
namespace Cons

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)

@[simp] def partial_op [Monad m] :
                  PartialOperator α (List α)
                                    (List α)
                                  Δα (ΔList α Δα)
                                    (ΔList α Δα)
                                  m where
  f a as   := pure <| a :: as
  δf_1 Δa  := pure <| ΔList.upd 0 [Δa]
  δf_2 | .ins i xs  => pure <| ΔList.ins (i + 1) xs
       | .del i n   => pure <| ΔList.del (i + 1) n
       | .upd i Δxs => pure <| ΔList.upd (i + 1) Δxs
variable [ChangeMonad m] [LawfulChangeMonad m]
open LawfulChangeMonad

theorem valid_1 : (partial_op (α:=α) (Δα:=Δα) m).valid_1 := by
  intro x y dx hv; cmsimp; grind

theorem valid_2 : (partial_op (α:=α) (Δα:=Δα) m).valid_2 := by
  intro x y dx hv; cases dx <;> cmsimp <;> grind

theorem correct_1 : (partial_op (α:=α) (Δα:=Δα) m).correct_1 := by
  intro x y dx hv; cmsimp

theorem correct_2 : (partial_op (α:=α) (Δα:=Δα) m).correct_2 := by
  intro x y dx hv; cmsimp
  cases dx with
  | ins i xs => simp
  | del i xs =>
    simp_all; solve_monad_eq
  | upd i xs =>
    simp_all; solve_monad_eq

def partial_spec : (partial_op (α:=α) (Δα:=Δα) m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m

def op [Monad m] := (partial_op (α:=α) (Δα:=Δα) m).toOperator
def spec := PartialOperator.toOperatorSpec (partial_op (α:=α) (Δα:=Δα) m) (partial_spec m)

end Cons
end ΔList
