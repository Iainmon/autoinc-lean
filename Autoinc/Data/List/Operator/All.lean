import Autoinc.Operator
import Autoinc.Data.List.Change
import Autoinc.Data.Bool.Change
import Autoinc.Lazy
@[simp] theorem List.take_all {α} (l : List α) (p : α → Bool) : l.all p = true → (l.take n).all p = true := by
  induction l generalizing n p with
  | nil => simp_all
  | cons x xs ih =>
    simp_all ; intros h₁ h₂ x_1 h₃
    match n with
    | .zero => simp_all
    | .succ n =>
      simp_all
      cases h₃; grind
      apply ih
      grind
      assumption
@[simp] theorem List.drop_all {α} (l : List α) (p : α → Bool) : l.all p = true → (l.drop n).all p = true := by
  induction l generalizing n p with
  | nil => simp_all
  | cons x xs ih =>
    simp_all ; intros h₁ h₂ x_1 h₃
    match n with
    | .zero => simp_all; cases h₃ <;> grind
    | .succ n =>
      simp_all
      apply ih
      grind
      assumption



namespace ΔList

namespace All

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type) [LazyMonadStateOf (List α) m]
  [MonadReaderOf (α → Bool) m]
  [MonadStateOf Bool m]
/-
The current laws do not suffice to model the predicate as a MonadReaderOf effect (two reads in the incremental run)
-/

@[simp] def Δf [Monad m] (dx : ΔList α Δα) : m ΔBool := do
  let oldRes : Bool ← MonadStateOf.get
  let pred ← read
  match dx, oldRes with
  | ins _ _, false => lazyModify (σ := List α) (·  ⨁ dx); pure ΔBool.noc
  | del _ _, true => lazyModify (σ := List α) (·  ⨁ dx); pure ΔBool.noc
  | ins _ xs, true =>
    lazyModify (σ := List α) (·  ⨁ dx)
    let newRes := xs.all pred
    set newRes
    pure (newRes ⊖ oldRes)
  | _, _ =>
    let cur ← (fun x : List α => x ⨁ dx) <$> getThe (List α)
    let newRes := cur.all pred
    set cur
    set newRes
    pure (newRes ⊖ oldRes)


@[simp] def op [Monad m]  : Operator (List α) Bool (ΔList α Δα) ΔBool m where
  f xs := do let pred ← read; let res := xs.all pred; set res; set xs; pure res
  Δf := Δf m
variable [ChangeMonad m] [LawfulChangeMonad m]
variable [LawfulLazyMonadStateOf (List α) m]

attribute [-simp] monadStateOf_get_eq_get
attribute [simp] Change.patch
theorem op_valid : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx hv ; cases x <;> cmsimp
variable  [LawfulMonadStateOf Bool m]
variable [IndependentStates Bool (List α) m]
variable [LawfulMonadReaderOf (α → Bool) m]
open LawfulChangeMonad LawfulLazyMonadStateOf LawfulMonadReaderOf LawfulMonadStateOf
attribute [grind =] List.take_append_drop List.mem_append List.all_eq

syntax "myrw" : tactic
macro_rules
| `(tactic|myrw) =>
  `(tactic|conv => {lhs; rhs; rw [Bool.and_comm]}; rw [←Bool.and_assoc, ←List.all_append, List.take_append_drop])
omit [LawfulChangeMonad m] in
theorem ins_correct : (op (α:=α) (Δα:=Δα) m).f (x ⨁ (ins i xs : ΔList α Δα)) = (op (α:=α) (Δα:=Δα) m).f x ⨁ (op (α:=α) (Δα:=Δα) m).Δf (ins i xs) := by
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
  match h:(x.all pred) with
  | true =>
    cmsimp
    rw [set_set_swap]
    solve_monad_eq
    split <;> split at * <;> try trivial
    grind only [List.all_eq]
  | false =>
    cmsimp; solve_monad_eq <;> myrw <;> grind
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
  match h:x.all pred with
  | true => cmsimp
  | false =>
    split <;> try trivial
    cmsimp ; split <;> split at * <;> rw [set_set_swap] <;> grind

omit [LawfulChangeMonad m] in
theorem upd_correct  : (op (α:=α) (Δα:=Δα) m).f (x ⨁ (upd i ds : ΔList α Δα)) = (op (α:=α) (Δα:=Δα) m).f x ⨁ (op (α:=α) (Δα:=Δα) m).Δf (upd i ds) := by
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
    conv =>
      rhs; intro
      rhs; intro
      rw [monadStateOf_get_eq_get, set_bind_get_bind]
      rw [←bind_assoc, set_bind_set, set_set_swap]
    conv =>
      rhs; intro
      rw [←bind_assoc, set_bind_set]
      rw [set_set_swap]
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







end All


end ΔList
