import Autoinc.Operator
import Autoinc.Lazy
import Autoinc.Data.List.Change
import Autoinc.Data.Bool.Change


namespace List
variable {α : Type} (l : List α) (p : α → Bool) (i : Nat)
theorem take_any_false : l.any p = false → (l.take i).any p = false := by
  induction l generalizing p i with
  | nil => simp_all
  | cons x xs ih =>
    intro h₁
    simp_all
    intro x_1 h₂
    cases i with
    | zero => simp_all
    | succ i =>
      rw [take_cons] at h₂; simp_all ; cases h₂; grind
      apply ih; grind
      assumption
      omega

theorem drop_any_false : l.any p = false → (l.drop i).any p = false := by
  induction l generalizing p i with
  | nil => simp_all
  | cons x xs ih =>
    intro h₁
    simp_all
    intro x_1 h₂
    cases i with
    | zero => simp_all; cases h₂ <;> grind only
    | succ i =>
      simp_all
      apply ih
      grind
      assumption


end List

namespace ΔList

namespace Any

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type) [LazyMonadStateOf (List α) m] [MonadStateOf Bool m] [MonadReaderOf (α → Bool) m]
/-
The current laws do not suffice to model the predicate as a MonadReaderOf effect (two reads in the incremental run)
-/

@[simp] def Δf [Monad m] (dx : ΔList α Δα) : m ΔBool := do
  let pred ← read
  let oldRes : Bool ← MonadStateOf.get
  match dx, oldRes with
  | ins _ _, true => lazyModify (fun x : List α => x ⨁ dx); pure ΔBool.noc
  | del _ _, false => lazyModify (fun x : List α => x ⨁ dx); pure ΔBool.noc
  | ins _ xs, false =>
    lazyModify (fun x : List α => x ⨁ dx)
    let newRes := xs.any pred
    set newRes
    pure (newRes ⊖ oldRes)
  | _, _ =>
    let cur ← (fun x : List α => x ⨁ dx) <$> getThe (List α)
    let newRes := cur.any pred
    set cur
    set newRes
    pure (newRes ⊖ oldRes)


@[simp] def op [Monad m]  : Operator (List α) Bool (ΔList α Δα) ΔBool m where
  f xs := do let pred ← read; let res := xs.any pred; set res; set xs; pure res
  Δf := Δf m

variable [ChangeMonad m] [LawfulChangeMonad m]
variable [LawfulLazyMonadStateOf (List α) m]
variable [LawfulMonadReaderOf (α → Bool) m]

attribute [-simp] monadStateOf_get_eq_get
attribute [simp] Change.patch
theorem op_valid : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx hv ; cases x <;> cmsimp

variable  [LawfulMonadStateOf Bool m]
variable [IndependentStates Bool (List α) m]
open LawfulChangeMonad LawfulLazyMonadStateOf LawfulMonadReaderOf LawfulMonadStateOf
syntax "myrw" : tactic
macro_rules
| `(tactic|myrw) =>
  `(tactic|
    { conv => lhs; rhs; rw [Bool.or_comm]
      rw [←Bool.or_assoc, ←List.any_append, List.take_append_drop]; grind
    }
  )

attribute [grind =] List.take_append_drop List.mem_append List.any_eq
omit [LawfulChangeMonad m] in
theorem ins_correct (hv : x ⊢ (ins i xs : ΔList α Δα)) : (op (α:=α) (Δα:=Δα) m).f (x ⨁ (ins i xs : ΔList α Δα)) = (op (α:=α) (Δα:=Δα) m).f x ⨁ (op (α:=α) (Δα:=Δα) m).Δf (ins i xs) := by
  cmsimp
  conv =>
    rhs
    conv =>
      rhs
      intro
      conv => rhs; intro
              rw [read_swap]
      rw [read_swap]
    rw [read_bind_read]
  congr 1
  funext pred
  match h:(x.any pred) with
  | true =>
    cmsimp
    solve_monad_eq
    · cases hv with
      | inl hv =>
        simp only [hv, List.any_nil, Bool.false_or, ←List.any_append]
        grind only [List.any_eq, List.take_append_drop]
      | inr hv => myrw
    · cases hv with
      | inl hv =>
        simp only [hv, List.any_nil, Bool.false_or, ←List.any_append]
        grind only [List.any_eq, List.take_append_drop]
      | inr hv => myrw
  | false =>
    cmsimp
    match h:(xs.any pred) with
    | true =>
      cmsimp; rw [set_set_swap]
    | false =>
      cmsimp; rw [set_set_swap]
      solve_monad_eq <;> rw [←List.any_append, List.take_append_drop] <;> grind

attribute [local grind =] List.drop_any_false List.take_any_false
omit [LawfulChangeMonad m] in
theorem del_correct  : (op (α:=α) (Δα:=Δα) m).f (x ⨁ (del i k : ΔList α Δα)) = (op (α:=α) (Δα:=Δα) m).f x ⨁ (op (α:=α) (Δα:=Δα) m).Δf (del i k) := by
  cmsimp
  conv =>
    rhs
    conv =>
      rhs
      intro
      conv => rhs; intro
              rw [read_swap]
      rw [read_swap]
    rw [read_bind_read]
  congr 1
  funext pred
  rw [set_set_swap]
  match h:x.any pred with
  | true =>
    cmsimp
    solve_monad_eq
    split <;> grind
  | false =>
    cmsimp
    rw [set_set_swap]
    solve_monad_eq <;> grind


omit [LawfulChangeMonad m] in
theorem upd_correct : (op (α:=α) (Δα:=Δα) m).f (x ⨁ (upd i ds : ΔList α Δα)) = (op (α:=α) (Δα:=Δα) m).f x ⨁ (op (α:=α) (Δα:=Δα) m).Δf (upd i ds) := by
  cmsimp
  conv =>
    rhs
    conv =>
      rhs
      intro
      conv => rhs; intro
              rw [read_swap]
      rw [read_swap]
    rw [read_bind_read]
    unfold getThe
    simp only [monadStateOf_get_eq_get]

    conv =>
      rhs; intro
      rw [set_set_swap]
      rhs; intro
      rw [←bind_assoc, set_bind_get]
      simp
      simp only [map_eq_pure_bind]
      simp only [get, getThe]
      rw [←bind_assoc, set_left_get_right_comm]
      simp
      simp only [map_eq_pure_bind]
      rhs; intro; rw [set_set_swap]
      rhs; intro; rw [←bind_assoc, set_bind_set]
    simp only [monadStateOf_get_eq_get]
    rhs; intro; rw [←bind_assoc, set_bind_get]
    simp
    simp only [map_eq_pure_bind]
  congr 1
  funext pred
  rw [set_set_swap]
  solve_monad_eq
  split <;> split at * <;> grind
omit [LawfulChangeMonad m] in
theorem op_correct : (op (α:=α) (Δα:=Δα) m).correct := by
  intro x dx hv
  cases dx with
  | ins i xs => grind [ins_correct]
  | del i k => grind [del_correct]
  | upd i ds => grind [upd_correct]


def spec : (op (α:=α) (Δα:=Δα) m).spec where
  valid := op_valid m
  correct := op_correct m

end Any


end ΔList
