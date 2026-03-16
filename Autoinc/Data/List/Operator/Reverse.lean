import Autoinc.Operator
import Autoinc.Data.List.Change

namespace List
attribute [grind cases] List.Forall₂ List
variable {α β : Type} (f : α → β → Prop)
theorem forall₂_app (xs₁ xs₂ : List α) (ys₁ ys₂ : List β) :
  List.Forall₂ f xs₁ ys₁ →
  List.Forall₂ f xs₂ ys₂ →
  List.Forall₂ f (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction xs₁ generalizing xs₂ ys₁ ys₂ with
  | nil => simp_all; grind
  | cons hd tl ih =>
    intro h
    match ys₁ with
    | nil => grind
    | cons _ _ => simp_all


theorem forall₂_rev (xs : List α) (ys : List β) :
  List.Forall₂ f xs ys →
  List.Forall₂ f xs.reverse ys.reverse := by
  induction xs generalizing ys with
  | nil => intro h; simp_all ; grind
  | cons hd tl tail_ih =>
    intro h; simp_all
    match ys with
    | List.nil => grind
    | List.cons Δhd Δtl =>
      simp_all
      obtain ⟨h₁, h₂⟩ := h
      specialize (tail_ih _ h₂)
      apply forall₂_app; grind; simp; grind


end List

namespace ΔList
namespace Reverse

variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type) [MonadStateOf Nat m] -- state is the length of input
@[simp] def op [Monad m] :
    Operator (List α) (List α)
             (ΔList α Δα) (ΔList α Δα)
             m where
  f xs := modifyGet (fun _ => (xs.reverse, xs.length))
  Δf Δl := do
    match Δl with
    | ins i [] => pure (ins i [])
    | ins i (x :: xs)  => modifyGet (fun len =>
        let n := (x :: xs).length; (ins (len - i) (x :: xs).reverse, len + n)
      )
    | del i 0 => pure (del i 0)
    | del i (n + 1) => modifyGet (fun len => (del (len - i - (n + 1)) (n + 1), len - (n + 1)))
    | upd i [] => pure (upd i [])
    | upd i dxs  =>
      let len ← get
      pure <| ΔList.upd (len - i - dxs.length) dxs.reverse

variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf Nat m]
open LawfulChangeMonad LawfulMonadStateOf
attribute [local simp] List.drop_reverse List.take_reverse List.drop_take
theorem op_valid : (op (α:=α) (Δα:=Δα) m).valid := by
  intro x dx h
  match dx with
  | ins i [] => cmsimp
  | ins i (x :: xs) => cmsimp
  | del i 0 => cmsimp
  | del i (Nat.succ _) => cmsimp ; set_elim ; grind
  | upd i [] => cmsimp
  | upd i Δxs@(hd :: tl) =>
    cmsimp ; set_elim
    match h with
    | ⟨h₂, h₃⟩ =>
      apply And.intro
      · omega
      · simp_all
        have : tl.reverse ++ [hd] = (hd :: tl).reverse := by grind
        rw [this]
        apply List.forall₂_rev
        have : (x.length - (x.length - i - (tl.length + 1)) - (x.length - (x.length - i - (tl.length + 1)) - (tl.length + 1))) = tl.length + 1 := by omega
        rw [this]
        have : x.length - (x.length - i - (tl.length + 1)) - (tl.length + 1) = i := by omega
        rw [this]; trivial



theorem op_correct : (op (α:=α) (Δα:=Δα) m).correct := by
  intro x dx h
  cases dx with
  | ins i xs =>
    cases xs with
    | nil => simp_all
    | cons hd tl =>
      cmsimp; solve_monad_eq; omega
      congr; omega; omega
  | del i n =>
    cases n with
    | zero => simp_all
    | _ => cmsimp ; solve_monad_eq; grind ; congr <;> grind
  | upd i Δxs =>
    cases Δxs with
    | nil => simp_all
    | _ =>
      cmsimp; solve_monad_eq; grind
      congr
      grind
      rw [List.reverse_zipWith]
      congr <;> try grind
      simp ; grind
      omega

def spec : (op (α:=α) (Δα:=Δα) m).spec where
  valid := op_valid m
  correct := op_correct m


end Reverse
end ΔList
