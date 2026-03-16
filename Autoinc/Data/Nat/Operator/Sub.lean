import Autoinc.Partial
import Autoinc.Data.Nat.Change

namespace ΔNat
namespace Sub
open ΔNat
variable (m : Type → Type) [MonadStateOf (Nat × Nat) m]

/-
To avoid costly branches, we simply use recomputation and difference to implement the ΔSub operator.
-/

@[simp] def partial_op [Monad m] : PartialOperator Nat Nat Nat ΔNat ΔNat ΔNat m where
  f x y := modifyGet (fun _ => (x - y, ⟨x, y⟩))
  δf_1 dx := modifyGet
    (fun ⟨x, y⟩ => let x' := x ⨁ dx; ((x' - y) ⊖ (x - y), (x', y)))
  δf_2 dy := modifyGet
    (fun ⟨x, y⟩ => let y' := y ⨁ dy; ((x - y') ⊖ (x - y), (x, y')))

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf (Nat × Nat) m]

open LawfulChangeMonad LawfulMonadStateOf
theorem valid_1 : (partial_op m).valid_1 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq, Difference.diff] <;> apply mprop_bind_const_pure <;> split <;> grind

theorem valid_2 : (partial_op m).valid_2 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq, Difference.diff] <;> apply mprop_bind_const_pure <;> split <;> grind

theorem correct_1 : (partial_op m).correct_1 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq, Difference.diff] <;> congr <;> funext <;> congr <;> split <;> grind

theorem correct_2 : (partial_op m).correct_2 := by
  intro a b dx hv
  cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq, Difference.diff] <;> congr <;> funext <;> congr <;> split <;> grind

def partial_spec : (partial_op m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m
def op [Monad m] := (partial_op m).toOperator
def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

end Sub
end ΔNat
