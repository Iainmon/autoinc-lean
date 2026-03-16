import Autoinc.Partial
import Autoinc.Lazy
import Autoinc.Data.List.Change
namespace List
attribute [local grind cases] List.Forall₂ List Nat
variable {α β : Type} (f : α → β → Prop)
theorem forall₂_drop (xs : List α) (ys : List β) (n : Nat) :
  List.Forall₂ f xs ys →
  List.Forall₂ f (xs.drop n) (ys.drop n) := by
  induction xs generalizing ys n with
  | nil => simp_all; grind
  | cons hd tl ih =>
    intro h
    match n with
    | Nat.zero => simp_all
    | Nat.succ n =>
      match ys with
      | [] => cases h
      | _ :: _ => simp_all
end List



namespace ΔList

namespace Drop

open ΔNat
variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)
variable [MonadStateOf (Nat × Nat) m]
variable [LazyMonadStateOf (List α) m]


@[simp] def δf_1 [Monad m] (dx : ΔList α Δα) : m (ΔList α Δα) := do
  let (n, length) ← MonadStateOf.get
  match dx with
  | ins i ys =>
    set (n, length + ys.length)
    if i < n then
      let (l : List α) ← MonadStateOf.get
      let xs' := l ⨁ dx
      set xs'
      pure (ins 0 ((xs'.drop n).take (ys.length)))
    else
      lazyModify (fun x : List α => x ⨁ dx)
      pure (ins (i - n) ys)
  | del i k =>
    set (n, length - k)
    lazyModify (fun x : List α => x ⨁ dx)
    let dellen := min k (length - n)
    pure (del (i - n) dellen)
  | upd i dts =>
    lazyModify (fun x : List α => x ⨁ dx)
    pure (upd (i - n) (dts.drop (n - i)))


@[simp] def δf_2 [Monad m] (dy : ΔNat) : m (ΔList α Δα) := do
  let (n, length) ← MonadStateOf.get (σ:=Nat×Nat)
  let (xs : List α) ← MonadStateOf.get
  match dy with
  | .inc k =>
    set (n + k, length)
    pure (del 0 (min k (xs.length - n)))
  | .dec k =>
    set (n - k, length)
    pure (ins 0 ((xs.drop (n - k)).take k))




@[simp] def partial_op [Monad m] : PartialOperator (List α) Nat (List α) (ΔList α Δα) ΔNat ((ΔList α Δα)) m where
  f x n := do set (n, x.length); set x; pure (x.drop n)
  δf_1 := δf_1 m
  δf_2 := δf_2 m

def op [Monad m] := (partial_op (α:=α) (Δα:=Δα) m).toOperator

variable [CM: ChangeMonad m] [LawfulChangeMonad m]
variable [LawfulMonadStateOf (Nat × Nat) m]
variable [LawfulLazyMonadStateOf (List α) m]
variable [IndependentStates (Nat × Nat) (List α) m]
open LawfulChangeMonad LawfulMonadStateOf LawfulLazyMonadStateOf

theorem valid_1_ins (x : List α) (i : Nat) (xs : List α) (n : Nat) :
  Change.valid (Δα:=ΔList α Δα) x (ins i xs) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (ins i xs) := by
  intro hv
  cases hv with
  | inl hv =>
    cmsimp
    rw [set_set_swap]
    cmsimp
    split <;> cmsimp
  | inr hv =>
    cmsimp
    rw [set_set_swap]
    cmsimp
    split <;> cmsimp <;> rw [set_set_swap] <;> cmsimp
    apply pure_2; grind

theorem valid_1_del (x : List α) (i k n : Nat) :
  Change.valid (Δα:=ΔList α Δα) x (del i k) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (del i k) := by
    intro hv; cmsimp;
    rw [set_set_swap] ; cmsimp
    rw [set_set_swap] ; cmsimp
    apply pure_2
    rcases hv <;> grind

attribute [local grind =] List.drop_of_length_le List.take_of_length_le
theorem valid_1_upd (x : List α) (i n : Nat) (dxs : List Δα) :
  Change.valid (Δα:=ΔList α Δα) x (upd i dxs) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (upd i dxs) := by
    intro hv; cmsimp;
    rw [set_set_swap] ; cmsimp
    rw [set_set_swap] ; cmsimp
    apply pure_2
    rcases hv
    grind
    rename_i h
    obtain ⟨h₁, h₂⟩ := h
    by_cases h₃ : x.length < n
    · right; apply And.intro
      · grind
      · have h_1 : n + (i - n) = n := by omega
        simp_all
        have h_2 : x.drop n = [] := by grind
        have h_3 : dxs.drop (n - i) = [] := by grind
        rw [h_2, h_3]; simp_all
    · by_cases h₄ : i ≤ n <;> by_cases h₅ : dxs.length ≤ n - i
      · right
        have h_1 : x.length - n + (n - i) = x.length - i := by omega
        simp_all [List.drop_of_length_le]
      · right
        apply And.intro; omega
        simp_all [List.take_drop]
        have h_1 : n + (i - n) = n := by omega
        have h_2 : n + (dxs.length - (n - i)) = i + dxs.length := by omega
        simp_all
        obtain h_3 := List.forall₂_drop _ _ _ (n - i) h₂
        simp_all [List.drop_drop]
      · simp_all
      · simp_all
        have h_1 : n + (i - n) = i := by omega
        simp_all [List.take_drop]
        have h_2 : n - i = 0 := by omega
        simp_all
        right
        omega

theorem valid_1 : (partial_op (α:=α) (Δα:=Δα) m).valid_1 := by
  intro x y dx hv
  cases dx with
  | ins i xs => grind [valid_1_ins]
  | del i k => grind [valid_1_del]
  | upd i dxs => grind [valid_1_upd]

theorem correct_1_ins (x : List α) (i : Nat) (xs : List α) (n : Nat) (hv :
  Change.valid (Δα:=ΔList α Δα) x (ins i xs)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (ins i xs) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (ins i xs)) n := by
    cmsimp
    rw [set_set_swap] ; cmsimp
    split
    · rw [set_set_swap]; cmsimp; solve_monad_eq; grind
      cases hv with
      | inl hv =>
        cmsimp
      | inr hv =>
        simp only [List.drop_append, List.length_take]
        have h_1 : List.drop n (List.take i x) = [] := by grind
        rw [h_1]
        simp_all
        simp only [List.take_append, List.length_drop]
        have h_2 : List.take xs.length (List.drop (n - i) xs) = xs.drop (n - i) := by grind
        rw [h_2, List.append_assoc]
        congr 1
        by_cases h₂ : xs.length < n - i
        · have : xs.length - (n - i) = 0 := by omega
          have : i + (n - i - xs.length) = n - xs.length := by omega
          simp_all [List.take_drop]
          have : n - xs.length + xs.length = n := by omega
          simp_all
          by_cases h₃ : n ≤ x.length
          · rw [←List.drop_append_of_le_length]
            congr ; simp_all; simp
            omega
          · simp_all
            grind only [LawfulChangeMonad.mk, = List.drop_append, List.append_nil, = List.take_take,
              = List.take_add, = List.length_take, List.length_append, List.take_of_length_le, →
              List.eq_nil_of_append_eq_nil, List.drop_of_length_le]
        · have : xs.length - (xs.length - (n - i)) = n - i := by omega
          simp_all
          have : List.drop n x = List.drop (n - i) (List.drop i x) := by simp_all [List.drop_drop]
          rw [this]
          simp only [List.take_append_drop]
    · rw [set_set_swap]; cmsimp; solve_monad_eq; grind
      simp_all [List.take_drop]
      by_cases h₃ : n ≤ x.length
      · rw [List.drop_append_of_le_length]
        simp_all; omega
      · simp_all
        have : List.drop n (List.take i x) = [] := by grind
        rw [this]
        simp_all
        cases hv
        simp_all
        grind
        omega

theorem correct_1_del (x : List α) (i n k : Nat) (hv :
  Change.valid (Δα:=ΔList α Δα) x (del i k)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (del i k) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (del i k)) n :=
  by
    cmsimp;
    rw [set_set_swap] ; cmsimp
    rw [set_set_swap] ; cmsimp
    solve_monad_eq; grind
    cases hv; simp_all
    have : List.drop (n + (i - n)) x = List.drop (i - n) (List.drop n x) := by simp_all [List.drop_drop]
    rw [this]
    simp only [List.take_append_drop]
    have : min i x.length = i := by omega
    have : i + (x.length - (i + k)) - n = x.length - k - n := by omega
    simp_all [List.drop_append, List.drop_take, List.length_take]
    by_cases h₁ : x.length ≤ n
    · have : i - n = 0 := by omega
      have : i + k + (n - i) = n + k := by omega
      simp_all
      grind
    · simp_all
      by_cases h₂ : i ≤ n
      · have : i - n = 0 := by omega
        have : i + k + (n - i) = n + k := by omega
        simp_all
        by_cases h₃ : k ≤ x.length - n
        · simp_all
        · simp_all
          have : min k (x.length - n) = x.length - n := by omega
          simp_all
          grind
      · simp_all
        have : n - i = 0 := by omega
        simp_all
        by_cases h₃ : k ≤ x.length - n
        · simp_all; congr 1; omega
        · simp_all
          have : min k (x.length - n) = x.length - n := by omega
          simp_all
          grind
theorem correct_1_upd (x : List α) (i : Nat) (dxs : List Δα) (hv :
  Change.valid (Δα:=ΔList α Δα) x (upd i dxs)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (upd i dxs) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (upd i dxs)) n :=
  by
    simp_all
    cmsimp
    rw [set_set_swap] ; cmsimp
    rw [set_set_swap] ; cmsimp
    solve_monad_eq; grind
    cases hv with
    | inl hv =>
      simp_all
      have : List.drop (n + (i - n)) x = List.drop (i - n) (List.drop n x) := by simp_all
      rw [this, List.take_append_drop]
    | inr hv =>
      obtain ⟨h₁, h₂⟩ := hv
      simp only [List.drop_append, List.length_take, List.drop_take]
      congr 1
      have :  min i x.length = i := by omega
      simp_all
      congr 1
      · simp only [List.drop_zipWith, List.drop_take, List.drop_drop]
        congr 3
        omega
      · congr 1
        omega

theorem correct_1 : (partial_op (α:=α) (Δα:=Δα) m).correct_1 := by
  intro x y dx hv
  cases dx with
  | ins i xs => apply correct_1_ins; grind
  | del i k => apply correct_1_del; grind
  | upd i dxs => apply correct_1_upd; grind

theorem valid_2 : (partial_op (α:=α) (Δα:=Δα) m).valid_2 := by
  intro x y dy hv
  cases dy with
  | inc a =>
    cmsimp;
    rw [set_set_swap] ; cmsimp
    rw [set_set_swap] ; cmsimp
    apply pure_2; grind
  | dec a =>
    cmsimp; rw [set_set_swap] ; cmsimp

theorem correct_2 : (partial_op (α:=α) (Δα:=Δα) m).correct_2 := by
  intro x y dy hv
  cases dy with
  | inc a =>
    cmsimp;
    rw [set_set_swap] ; cmsimp;
    rw [set_set_swap] ; cmsimp;
    rw [set_set_swap]
    solve_monad_eq; grind
  | dec a =>
    cmsimp;
    rw [set_set_swap] ; cmsimp;
    rw [set_set_swap] ; cmsimp;
    rw [set_set_swap]
    solve_monad_eq
    have : List.drop y x = List.drop a (List.drop (y - a) x) := by simp_all; grind
    rw [this, List.take_append_drop]


def partial_spec : (partial_op (α:=α) (Δα:=Δα) m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m

def spec := PartialOperator.toOperatorSpec (partial_op (α:=α) (Δα:=Δα) m) (partial_spec m)



end Drop



end ΔList
