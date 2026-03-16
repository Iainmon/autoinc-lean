import Autoinc.Partial
import Autoinc.Data.Nat.Change

namespace ΔNat
namespace Mul

variable (m : Type → Type)  [MonadStateOf (Nat × Nat) m]

@[simp] def partial_op [Monad m] : PartialOperator Nat Nat Nat ΔNat ΔNat ΔNat m where
  f x y := modifyGet (fun _ => (x * y, (x, y)))
  δf_1 | .inc n => modifyGet (fun (x, y) => (.inc (n * y), (x + n, y)))
       | .dec n => modifyGet (fun (x, y) => (.dec (n * y), (x - n, y)))
  δf_2 | .inc n => modifyGet (fun (x, y) => (.inc (n * x), (x, y + n)))
       | .dec n => modifyGet (fun (x, y) => (.dec (n * x), (x, y - n)))

attribute [local simp] Nat.sub_mul
  Nat.mul_sub_left_distrib Nat.mul_sub_right_distrib
  Nat.add_mul Nat.mul_add

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf (Nat × Nat) m]
open LawfulChangeMonad LawfulMonadStateOf
theorem valid_1 : (partial_op m).valid_1 := by
  simp
  intro a b dx hv
  match dx with
  | .inc da =>
    simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
  | .dec c =>
    cmsimp
    apply mprop_bind_const_pure
    apply Nat.mul_le_mul_right
    grind

theorem valid_2 : (partial_op m).valid_2 := by
  simp
  intro a b dx hv
  match dx with
  | .inc da =>
    simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
  | .dec c =>
    simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
    apply mprop_bind_const_pure
    grind [Nat.mul_comm, Nat.mul_le_mul_left]


theorem correct_1 : (partial_op m).correct_1 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]


theorem correct_2 : (partial_op m).correct_2 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
  <;> congr <;> funext <;> congr 2 <;> simp [Nat.mul_comm]

def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op m).toOperator
def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

end Mul
end ΔNat
