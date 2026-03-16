import Autoinc.Partial
import Autoinc.Lazy
import Autoinc.Data.List.Change


namespace List
attribute [local grind cases] List.Forall₂ List Nat
variable {α β : Type} (f : α → β → Prop)
theorem forall₂_take (xs : List α) (ys : List β) (n : Nat) :
  List.Forall₂ f xs ys →
  List.Forall₂ f (xs.take n) (ys.take n) := by
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

namespace Take
open ΔNat
variable {α Δα : Type} [Change α Δα]
variable (m : Type → Type)
variable [MonadStateOf (Nat × Nat) m]
variable [LazyMonadStateOf (List α) m]


@[simp] def δf_1 [Monad m] (dy : ΔList α Δα) : m (List (ΔList α Δα)) := do
  let (n, length) ← MonadStateOf.get
  match dy with
  | ins i ys => do
    lazyModify (fun x : List α => x ⨁ dy)
    let new := ys.take (n - i)
    let newlen := min ys.length (n - i)
    let missing := n - length
    let dellen := newlen - missing
    let remaining := n - i - ys.length
    set (n, length + ys.length)
    pure [ΔList.del (i + remaining) dellen, ΔList.ins i new]
  | del i k =>
    if n ≤ i then
      lazyModify (fun x : List α => x ⨁ dy)
      set (n, length - k)
      pure []
    else
      let xs' ← MonadStateOf.get (σ:=List α)
      let dellen := min k (n - i)
      let remaining := n - i - k
      lazyModify (fun x : List α => x ⨁ dy)
      set (n, length - k)
      pure [ΔList.del i dellen, ΔList.ins (i + remaining) ((xs'.drop (i + k + remaining)).take dellen)]
  | upd i ds => do
    lazyModify (fun x : List α => x ⨁ dy)
    pure [upd i (ds.take (n - i))]

@[simp] def δf_2 [Monad m] (dk : ΔNat) : m (List (ΔList α Δα)) := do
  let ((n, length) : Nat × Nat) ← MonadStateOf.get
  let l : List α ← MonadStateOf.get
  match dk with
  | inc c => do
    set (n + c, length)
    pure [ins n ((l.drop n).take c)]
  | dec c => do
    let n' := n - c
    set (n', length)
    if n' > l.length then
      pure []
    else if n > l.length then
      pure [del n' (l.length - n')]
    else
      pure [del n' c]

@[simp] def partial_op [Monad m] : PartialOperator (List α) Nat (List α) (ΔList α Δα) ΔNat (List (ΔList α Δα)) m where
  f x n := do set (n, x.length); set x; pure <| x.take n
  δf_1 := δf_1 m
  δf_2 := δf_2 m

def op [Monad m] := (partial_op (α:=α) (Δα:=Δα) m).toOperator


variable [CM: ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf (Nat × Nat) m] [LawfulLazyMonadStateOf (List α) m]
variable [IndependentStates (Nat × Nat) (List α) m]



open LawfulChangeMonad LawfulMonadStateOf LawfulLazyMonadStateOf
theorem valid_1_ins (x : List α) (i : Nat) (xs : List α) (n : Nat) :
  Change.valid (Δα:=ΔList α Δα) x (ins i xs) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (ins i xs) := by
  intro hv; cmsimp
  rw [set_set_swap]
  cmsimp
  rw [set_set_swap]
  cmsimp
  apply pure_2
  simp [Change.valid]; grind

theorem valid_1_del (x : List α) (i k n : Nat) :
  Change.valid (Δα:=ΔList α Δα) x (del i k) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (del i k) := by
    intro hv; cmsimp;
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    split
    cmsimp
    monad_simp
    cmsimp
    apply pure_2
    simp [Change.valid]; grind



theorem valid_1_upd (x : List α) (i n : Nat) (dxs : List Δα) :
  Change.valid (Δα:=ΔList α Δα) x (upd i dxs) → (partial_op (α:=α) (Δα:=Δα) m).f x n ⊢ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (upd i dxs) := by
    intro hv; cmsimp;
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    cmsimp
    apply pure_2
    rcases hv <;> simp [Change.valid]
    grind
    rename_i h
    obtain ⟨h₁, h₂⟩ := h
    by_cases h₃ : x.length < n
    · right; apply And.intro
      · grind
      · have h₄: dxs.take (n - i) = dxs := by grind [List.take_of_length_le]
        have h₅ : min (n - i) dxs.length = dxs.length := by grind
        have h₆ : x.take n = x := by grind [List.take_of_length_le]
        grind
    · simp_all
      by_cases h₄ : n < i
      · grind
      · simp_all
        right; apply And.intro
        · grind
        · by_cases h₅ : n < i + dxs.length
          · have h₆ : min (n - i) dxs.length = n - i := by grind
            simp_all [List.take_drop, List.take_take]
            have h₇ : i + (n - i) = n := by grind
            simp_all [List.drop_take]
            have h₈ : (List.take dxs.length (List.drop i x)).take (n - i) = List.take (n - i) (List.drop i x) := by grind
            rw [←h₈]
            apply List.forall₂_take
            grind
          · simp_all
            have h₇ : min (n - i) dxs.length = dxs.length := by grind
            simp_all [List.take_drop, List.take_take]
            simp_all [List.drop_take]
            have h₈ : List.take (n - i) dxs = dxs := by grind [List.take_of_length_le]
            grind


theorem valid_1 : (partial_op (α:=α) (Δα:=Δα) m).valid_1 := by
  intro x y dx hv
  cases dx with
  | ins i xs => grind [valid_1_ins]
  | del i k => grind [valid_1_del]
  | upd i dxs => grind [valid_1_upd]

theorem correct_1_ins (x : List α) (i : Nat) (xs : List α) (n : Nat) (hv :
  Change.valid (Δα:=ΔList α Δα) x (ins i xs)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (ins i xs) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (ins i xs)) n := by
    simp_all
    cmsimp
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    solve_monad_eq
    grind
    cases hv
    simp_all
    simp_all [List.take_take, List.take_append]
    congr 1
    grind
    by_cases h₁ : x.length < n
    · have h₂ : min n x.length = x.length := by grind
      simp_all; clear h₂
      by_cases h₂ : n ≤ i + xs.length
      · have h₃ : min xs.length (n - i) = n - i := by grind
        simp_all
        have h₄ :  n - i - xs.length = 0 := by omega
        simp_all
        omega
      · simp_all
        have h₃ : i + (n - i - xs.length) = n - xs.length := by omega
        simp_all
        have h₄ : i - (n - xs.length) = 0 := by omega
        have h₅ : min xs.length (n - i) = xs.length := by omega
        simp_all
        by_cases h₆: x.length + xs.length ≤ n
        · have h₇ : min (n - xs.length) x.length = x.length := by omega
          simp_all
          have h₈ : n - xs.length + (xs.length - (n - x.length)) = n - xs.length := by omega
          simp_all
          have h₉ : List.take n x = x := by rw [List.take_of_length_le]; omega
          simp_all
          rw [List.take_of_length_le]; grind
        · have h₇ : min (n - xs.length) x.length = n - xs.length := by omega
          simp_all
          have h₈ : n - xs.length + (xs.length - (n - x.length)) = x.length := by omega
          simp_all
          have h₉ : List.drop x.length (List.take n x) = [] := by grind [List.drop_of_length_le]
          rw [h₉]
          simp_all [List.drop_take]
          grind
    · simp_all
      by_cases h₂ : n < i
      · have h₃ : i - min (i + (n - i - xs.length)) n = i - n := by omega
        simp_all
        have h₄ : n - i - xs.length = 0 := by omega
        simp_all
        have h₅ : n - i = 0 := by omega
        simp_all
        grind
      · by_cases h₂ : n < i + xs.length
        · have h₃ : min xs.length (n - i) = n - i := by grind
          simp_all
          have h₄ :  n - i - xs.length = 0 := by omega
          simp_all
        · simp_all
          have h₃ : i + (n - i - xs.length) = n - xs.length := by omega
          simp_all
          have h₄ : i - (n - xs.length) = 0 := by omega
          have h₅ : min xs.length (n - i) = xs.length := by omega
          simp_all
          have h₆ : n - xs.length + xs.length = n := by omega
          simp_all [List.drop_take]; omega


attribute [local grind =] List.take_of_length_le List.drop_of_length_le


theorem correct_1_del (x : List α) (i n k : Nat) (hv :
  Change.valid (Δα:=ΔList α Δα) x (del i k)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (del i k) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (del i k)) n :=
  by
    simp_all
    cmsimp
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    split
    · cmsimp
      rw [set_set_swap]
      solve_monad_eq
      congr 1 ; grind
      cases hv
      · simp_all
      · rw [List.take_append_of_le_length, List.take_take] <;> grind
    · cmsimp
      rw [set_set_swap]
      solve_monad_eq
      congr 1 ; grind
      cases hv
      simp_all
      simp_all [List.take_take, List.take_append]
      congr 1
      grind
      by_cases h₁ : x.length < n
      · have h₂ : min n x.length = x.length := by grind
        simp_all; clear h₂
        by_cases h₂ : n ≤ i + k
        · have h₃ : min k (n - i) = n - i := by grind
          simp_all
          have h₄ :  n - i - k = 0 := by omega
          simp_all
          omega
        · simp_all
          have h₃ : i + (n - i - k) = n - k := by omega
          have : i + k + (n - i - k) = n := by omega
          simp_all
          have h₄ : i - (n - k) = 0 := by omega
          have h₅ : min k (n - i) = k := by omega
          simp_all
          by_cases h₆: x.length + k ≤ n
          · have h₇ : min i x.length = i := by omega
            simp_all
            have : List.take (n - i) (List.drop (i + k) x) = List.drop (i + k) x := by rw [List.take_of_length_le]; simp; omega
            rw [this]
            have : List.take n x = x := by rw [List.take_of_length_le]; omega
            have : i + k + (n - i - k) = n := by omega
            simp_all
            have h₁₀ : [] = List.drop n x := by rw [List.drop_of_length_le]; omega
            rw [←h₁₀]
            have h₁₁ : min i n = i := by omega
            simp_all [List.drop_append]
            have : i + k + (n - k - i) = n := by omega
            simp_all
            have : List.drop n x = [] := by grind
            rw [this]
            simp_all
            have : List.drop (n - k) (List.take i x) = [] := by grind
            rw [this]
            rw [List.take_of_length_le]; grind
            simp; grind
          · have h₇ : min i x.length = i := by omega
            simp_all
            have h₈ : min i n = i := by omega
            simp_all
            have h₉ : List.drop x.length (List.take n x) = [] := by grind
            simp_all [List.drop_take]
            have : List.take (n - (i + k)) (List.drop (i + k) x) = List.drop (i + k) x := by grind
            simp_all
            have : List.take (n - k - i) (List.drop (i + k) x) = List.drop (i + k) x := by grind
            simp_all
            have : (List.take k (List.drop n x) ++ List.drop (n - k) (List.take i x ++ List.drop (i + k) x)) = [] := by grind
            rw [this]
            rw [List.take_of_length_le] <;> simp_all ; grind
      · simp_all
        by_cases n < i <;> by_cases n < i + k
        · have : (i + (n - i - k) - min i n) = i - n := by omega
          simp_all
          have : i + k + (n - i - k) = i + k := by omega
          simp_all
          have : min k (n - i) = n - i := by omega
          simp_all
          have : n - i = 0 := by omega
          simp_all
          have :  min i n = n := by omega
          rw [this]
          have : min i x.length = i := by omega
          rw [this]
          have : List.take (i - n) (List.drop i (List.take n x)) = [] := by grind
          rw [this]
          have : List.drop i (List.take n x) = [] := by grind
          simp_all
        · have : (i + (n - i - k) - min i n) = i - n := by omega
          simp_all
          have : i + k + (n - i - k) = i + k := by omega
          simp_all
          have : min k (n - i) = n - i := by omega
          simp_all
          have : n - i = 0 := by omega
          simp_all
          have :  min i n = n := by omega
          rw [this]
          have : min i x.length = i := by omega
          rw [this]
          have : List.take (i - n) (List.drop i (List.take n x)) = [] := by grind
          rw [this]
          have : List.drop i (List.take n x) = [] := by grind
          simp_all
        · have : (i + (n - i - k) - min i n) = i - n := by omega
          simp_all
          have : i + k + (n - i - k) = i + k := by omega
          simp_all
          have : min k (n - i) = n - i := by omega
          simp_all
          have : min i x.length = i := by omega
          rw [this]
        · have : (i + (n - i - k) - min i n) = n - i - k := by omega
          simp_all
          have : i + k + (n - i - k) = n := by omega
          simp_all
          have : min k (n - i) = k := by omega
          simp_all
          have : min i x.length = i := by omega
          rw [this]
          have : i + (n - i - k) = n - k := by grind
          simp_all [List.drop_append]
          have : i + k + (n - k - i) = n := by omega
          simp_all
          have : List.take (n - i - k) (List.drop (i + k) (List.take n x)) = List.drop (i + k) (List.take n x) := by grind
          simp_all
          have : List.drop (n - k) (List.take i x) = [] := by grind
          rw [this]
          simp [List.drop_take]
          simp [List.take_drop]
          have : i + k + (n - i) = n + k := by omega
          simp_all [List.take_add, List.drop_append]




theorem correct_1_upd (x : List α) (i : Nat) (dxs : List Δα) (hv :
  Change.valid (Δα:=ΔList α Δα) x (upd i dxs)) : (partial_op (α:=α) (Δα:=Δα) m).f x n ⨁ (partial_op (α:=α) (Δα:=Δα) m).δf_1 (upd i dxs) = (partial_op (α:=α) (Δα:=Δα) m).f (Change.patch (Δα:=ΔList α Δα) x (upd i dxs)) n :=
  by
    simp_all
    cmsimp
    rw [set_set_swap]
    cmsimp
    rw [set_set_swap]
    cmsimp
    solve_monad_eq
    grind
    solve_monad_eq
    cases hv
    simp_all
    simp [List.take_append, List.take_take]
    have : min i x.length = i := by omega
    simp_all
    congr 1; grind
    congr
    · simp [List.take_zipWith]
      congr 1
      simp [List.drop_take, List.take_take]
    · simp [List.drop_take]
      by_cases i + dxs.length ≤ n
      · have : min (n - i) dxs.length = dxs.length := by omega
        simp_all
        omega
      · simp_all
        have : min (n - i) dxs.length = n - i := by omega
        simp_all
        have : min dxs.length (x.length - i) = dxs.length := by omega
        simp_all
        have : n - (i + (n - i)) = 0 := by omega
        simp_all
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
    rw [set_set_swap]
    cmsimp;
    rw [set_set_swap]
    cmsimp
    apply pure_2
    simp [Change.valid] ; grind
  | dec a =>
    cmsimp;
    rw [set_set_swap]
    cmsimp;
    rw [set_set_swap]
    cmsimp
    split
    · cmsimp
    · split
      · cmsimp; apply pure_2; simp_all [Change.valid]; grind
      · cmsimp; apply pure_2; simp_all [Change.valid]

theorem correct_2 : (partial_op (α:=α) (Δα:=Δα) m).correct_2 := by
  intro x y dy hv
  cases dy with
  | inc a =>
    cmsimp;
    rw [set_set_swap]; cmsimp
    rw [set_set_swap]; cmsimp
    rw [set_set_swap]
    solve_monad_eq; grind
  | dec a =>
    cmsimp
    rw [set_set_swap]; cmsimp
    rw [set_set_swap]; cmsimp
    rw [set_set_swap]
    split <;> cmsimp
    · solve_monad_eq; grind
    · split <;> cmsimp <;> solve_monad_eq <;> simp_all [List.take_take] <;> grind



def partial_spec : (partial_op (α:=α) (Δα:=Δα) m).spec where
  valid_1 := valid_1 m
  valid_2 := valid_2 m
  correct_1 := correct_1 m
  correct_2 := correct_2 m

def spec := PartialOperator.toOperatorSpec (partial_op (α:=α) (Δα:=Δα) m) (partial_spec m)


end Take


end ΔList
