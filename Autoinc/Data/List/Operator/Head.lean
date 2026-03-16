import Autoinc.Operator
import Autoinc.Data.List.Change
import Autoinc.Data.Option.Change
import Autoinc.Lazy


namespace ΔList

namespace Head
variable {α Δα : Type} [Change α Δα] [Difference α Δα]
variable (m : Type → Type)
variable [LazyMonadStateOf (List α) m]

@[simp] def op [Monad m] : Operator (List α) (Option α) (ΔList α Δα) (ΔOption α Δα) m where
  f x := modifyGet (fun _ => (x.head?, x))
  Δf dx := do
    match dx with
    | ins 0 (y :: _) => modifyGet (fun x => (some y ⊖ x.head?, x ⨁ dx))
    | del 0 (n + 1) => modifyGet (fun x => (x[n + 1]? ⊖ x.head?, x ⨁ dx))
    | upd 0 (d :: _) => modifyGet (fun x => (ΔOption.change_some d, x ⨁ dx))
    | _ => lazyModifyThe (List α) (· ⨁ dx); pure ΔOption.noc

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulLazyMonadStateOf (List α) m]
open LawfulChangeMonad LawfulMonadStateOf

theorem op_valid : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx h
  match h₁:dx with
  | ins 0 (y :: ys) =>
    cmsimp; set_elim
    match h₂:x.head? with
    | none => simp_all [Difference.diff]
    | some hd => simp_all [Difference.diff]; apply Difference.diff_valid
  | del 0 (Nat.succ n) =>
    cmsimp; set_elim
    match h₂:x[n + 1]?, h₃:x.head? with
    | none, none => simp_all [Difference.diff]
    | none, some val => simp_all [Difference.diff]
    | some t, none => simp_all
    | some t, some v =>
      simp_all [Difference.diff]
      match h₄:x.head? with
      | none => simp_all
      | some v_1 =>
        have h₅:v= v_1:=by simp_all
        simp_all; apply Difference.diff_valid
  | upd 0 (d :: ds) =>
    cmsimp; set_elim
    match h₁:x.head? with
    | none => simp_all
    | some v =>
      have h_v : v ⊢ d := by match x with
      | [] => simp_all
      | _ :: _ => simp_all
      simp_all
  | ins 0 [] => cmsimp
  | ins (Nat.succ n) (x :: xs) => cmsimp
  | ins (Nat.succ n) [] => cmsimp
  | del (Nat.succ _) 0 => cmsimp
  | del (Nat.succ _) (Nat.succ _) => cmsimp
  | del 0 0 => cmsimp
  | upd 0 [] => cmsimp
  | upd (Nat.succ n) (x :: xs) => cmsimp
  | upd (Nat.succ _) [] => cmsimp

attribute [grind =] Difference.diff_correct
theorem op_correct : (op (α:=α) (Δα:=Δα) m).correct := by
  intro x dx h
  match h₁:dx with
  | ins 0 (y :: ys) =>
    cmsimp
    match x with
    | [] => simp_all [Difference.diff]
    | _ :: _ => cmsimp ; solve_monad_eq ; grind
  | del 0 (Nat.succ n) =>
    cmsimp
    match h₂:x[n + 1]?, h₃:x.head? with
    | none, none => simp_all [Difference.diff]
    | none, some val => simp_all [Difference.diff]
    | some t, none => simp_all
    | some t, some v =>
      simp_all
      match h₄:x.head? with
      | none => simp_all
      | some v_1 => cmsimp ; solve_monad_eq ; grind
  | upd 0 (d :: _) =>
    cmsimp
    match h₁:x.head? with
    | none => simp_all
    | some v =>
      simp_all
      match x with
      | [] => simp_all
      | _ :: _ => simp_all
  | ins 0 [] => cmsimp
  | ins (Nat.succ n) _ =>
    match x with
    | [] => cmsimp; solve_monad_eq
    | a :: as => cmsimp; solve_monad_eq
  | del (Nat.succ _) 0 => cmsimp
  | del (Nat.succ _) (Nat.succ _) =>
    match x with
    | [] => cmsimp; solve_monad_eq
    | _ :: _ => cmsimp ; solve_monad_eq ; grind
  | del 0 0 => cmsimp
  | upd _ [] => cmsimp
  | upd (Nat.succ n) (_ :: _) =>
    match x with
    | [] => cmsimp; solve_monad_eq
    | _ :: _ => cmsimp ; solve_monad_eq ; grind

def spec : (op (α:=α) (Δα:=Δα) m).spec where
  valid := op_valid m
  correct := op_correct m


end Head

end ΔList
