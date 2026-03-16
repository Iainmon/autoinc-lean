import Autoinc.Data.List.Change
import Autoinc.Partial

namespace ΔList

namespace Append
open List

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type) [MonadStateOf Nat m]
@[simp] def partial_op [Monad m] : PartialOperator (List α) (List α) (List α) (ΔList α Δα) (ΔList α Δα) (ΔList α Δα) m where
  f x y := modifyGet (fun _ => (x ++ y, x.length))
  δf_1 dx := modifyGet (fun n => (dx, n ⨁ dx.asDeltaNat))
  δf_2 dy := do pure (dy.setPos (dy.getPos + (←get)))


variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf Nat m]
open LawfulChangeMonad LawfulMonadStateOf

theorem valid_1 : (partial_op (α:=α) (Δα:=Δα) m).valid_1 := by
  intro x y dx hv
  match dx with
  | ins i xs => cmsimp; set_elim; grind
  | del i xs => cmsimp; set_elim; grind
  | upd i xs =>
    cmsimp; set_elim
    cases hv; grind; right
    have h₃ : xs.length - (x.length - i) = 0 := by omega
    grind [take_append]

theorem valid_2 : (partial_op (α:=α) (Δα:=Δα) m).valid_2 := by
  intro x y dx hv
  match dx with
  | ins i xs => cmsimp; set_elim; grind
  | del i xs => cmsimp; set_elim; grind
  | upd i xs =>
    cmsimp; set_elim
    cases hv; grind; right
    grind [drop_eq_nil_of_le]

attribute [simp ←] List.append_assoc
theorem correct_1 : (partial_op (α:=α) (Δα:=Δα) m).correct_1 := by
  intro x y dx hv
  cases dx with
  | ins i xs =>
    cmsimp; solve_monad_eq
    · grind
    · cases hv
      · simp_all only [append_nil, take_append_drop]
      · simp_all [drop_append, take_append]
  | del i xs =>
    cmsimp; solve_monad_eq
    · grind
    · cases hv
      · simp_all
      · simp_all [drop_append, take_append]; grind
  | upd i xs =>
    cmsimp; solve_monad_eq
    · grind
    · cases hv
      · simp_all
      · simp_all [drop_append, take_append]
        congr 2 <;> simp_all <;> grind

attribute [local grind =] take_of_length_le drop_of_length_le
theorem correct_2 : (partial_op (α:=α) (Δα:=Δα) m).correct_2 := by
  intro x y dx hv
  cases dx with
  | ins i xs =>
    cmsimp; solve_monad_eq; congr 1
    · simp [take_append]; grind
    · simp [drop_append]
  | del i xs =>
    cmsimp; solve_monad_eq; congr 1
    · simp [take_append]; grind
    · simp [drop_append]; grind
  | upd i xs =>
    cmsimp; solve_monad_eq; congr 1
    · simp [take_append]; congr 3
      grind
      cases hv <;> grind
    · simp [drop_append]; grind

def partial_spec : (partial_op (α:=α) (Δα:=Δα) m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op (α:=α) (Δα:=Δα) m).toOperator
def spec := PartialOperator.toOperatorSpec (partial_op (α:=α) (Δα:=Δα) m) (partial_spec m)

end Append


end ΔList
