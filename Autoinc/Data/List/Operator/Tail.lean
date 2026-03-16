import Autoinc.Operator
import Autoinc.Data.List.Change
import Autoinc.Data.Nat.Change
import Autoinc.Lazy
set_option maxHeartbeats 500000
namespace ΔList
attribute [local simp] Change.patch
namespace Tail
variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)
variable [LazyMonadStateOf (List α) m]
/-
Note: it's possible to optimize this operator by including the length into the state
-/
@[simp] def op [Monad m] : Operator (List α) (List α) (ΔList α Δα) (ΔList α Δα) m where
  f x := modifyGet (fun _ => (x.tail, x))
  Δf dx := do
    match dx with
    | ins 0 [] => pure $ ins 0 []
    | ins 0 (_ :: tl) =>
      modifyGet (fun x => (ins 0 (tl ++ x.take 1), x ⨁ dx))
    | ins (i + 1) xs => do
      lazyModify (fun x : List α => x ⨁ dx)
      pure $ ins i xs
    | del 0 n => modifyGet (fun x => let dy := if x.length == n then del 0 (n - 1) else del 0 n; (dy, x ⨁ dx))
    | del (i + 1) n => lazyModify (fun x : List α => x ⨁ dx); pure (del i n)
    | upd 0 ds => lazyModify (fun x : List α => x ⨁ dx); pure (upd 0 ds.tail)
    | upd (i + 1) ds => lazyModify (fun x : List α => x ⨁ dx); pure (upd i ds)

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulLazyMonadStateOf (List α) m]
open LawfulChangeMonad LawfulMonadStateOf

theorem op_valid : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx h
  match dx with
  | ins 0 [] => cmsimp
  | ins 0 (_ :: _) => cmsimp
  | ins (i + 1) xs => cmsimp; set_elim; grind
  | del 0 n => cmsimp; set_elim; simp [Change.valid] ; grind
  | del (i + 1) n => cmsimp; set_elim; grind
  | upd 0 ds =>
    cmsimp; set_elim
    cases h <;> cases x <;> cases ds <;> simp_all
  | upd (i + 1) ds => cmsimp; set_elim; grind


theorem op_correct : (op (α:=α) (Δα:=Δα) m).correct := by
  intro x dx h
  match dx with
  | ins 0 [] => cmsimp
  | ins 0 (_ :: _) => cmsimp ; solve_monad_eq ; grind [cases List]
  | ins (i + 1) xs => cmsimp; cases x <;> cmsimp
  | del 0 0 => cmsimp
  | del 0 n =>
    cmsimp; congr 1; funext; congr 1; split <;> split at * <;> try grind
    rw [List.drop_of_length_le] <;> simp_all; grind
  | del (i + 1) n =>
    cmsimp; congr; funext; congr 1; cases h
    · simp_all; cases x <;> simp_all
    · cases x <;> simp_all; grind
  | upd 0 ds =>
    cmsimp; solve_monad_eq
    cases h <;> cases x <;> cases ds <;> simp_all
  | upd (i + 1) ds =>
    cmsimp; congr; funext; congr 1; cases h
    · simp_all; cases x <;> simp_all
    · cases x <;> simp_all; grind





end Tail

end ΔList
