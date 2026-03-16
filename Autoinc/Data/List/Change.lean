import Autoinc.Change
import Autoinc.Data.Nat.Change
import Batteries.Data.List


/-- change representation for List -/
inductive ΔList α Δα : Type where
  | ins : Nat → List α → ΔList α Δα
  | del : Nat → Nat → ΔList α Δα
  | upd : Nat → List Δα → ΔList α Δα
  deriving Repr, BEq

instance [ToString α] [ToString Δα] : ToString (ΔList α Δα) where
  toString
    | ΔList.ins i ts => s!"ins {i} [{String.intercalate ", " (ts.map ToString.toString)}]"
    | ΔList.del i n => s!"del {i} {n}"
    | ΔList.upd i ds => s!"upd {i} [{String.intercalate ", " (ds.map ToString.toString)}]"

namespace ΔList
variable {α Δα : Type} [Change α Δα]

instance : Inhabited (ΔList α Δα) where
  default := .ins 0 []

/-- change class for List -/
instance ListChange : Change (List α) (ΔList α Δα) where
  patch xs d := match d with
  | .ins i ys =>
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ ys ++ xs₂
  | .del i n =>
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ xs₂.drop n
  | .upd i ds =>
    let (xs₁, xs₂) := List.splitAt i xs
    let (ys, zs) := List.splitAt ds.length xs₂
    xs₁ ++ ys.zipWith Change.patch ds ++ zs
  valid xs ds := match ds with
  | .ins i ys => ys.isEmpty ∨ i ≤ xs.length
  | .del i n => n = 0 ∨ i + n ≤ xs.length
  | .upd i ds => ds.isEmpty ∨
      i + ds.length ≤ xs.length ∧
        let ys := (xs.drop i).take ds.length
        List.Forall₂ Change.valid ys ds

@[simp] theorem ListChange.valid_ins {α Δα : Type} [Change α Δα]
  (xs ys : List α) (i : Nat) :
  xs ⊢ (ΔList.ins i ys : ΔList α Δα) ↔ ys.isEmpty ∨ i ≤ xs.length := by simp [Change.valid]
@[simp] theorem ListChange.valid_del {α Δα : Type} [Change α Δα]
  (xs : List α) (i n : Nat) :
  xs ⊢ (ΔList.del i n : ΔList α Δα) ↔ n = 0 ∨ i + n ≤ xs.length := by simp [Change.valid]
@[simp] theorem ListChange.valid_upd {α Δα : Type} [Change α Δα]
  (xs : List α) (i : Nat) (ds : List Δα) :
  xs ⊢ (ΔList.upd i ds : ΔList α Δα) ↔ ds.isEmpty ∨
    (i + ds.length ≤ xs.length ∧
      let ys := (xs.drop i).take ds.length
      List.Forall₂ Change.valid ys ds) := by simp [Change.valid]

@[simp] theorem ListChange.patch_ins {α Δα : Type} [Change α Δα]
  (xs ys : List α) (i : Nat) :
  xs ⨁ (ΔList.ins i ys : ΔList α Δα) =
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ ys ++ xs₂ := by simp [Change.patch]
@[simp] theorem ListChange.patch_del {α Δα : Type} [Change α Δα]
  (xs : List α) (i n : Nat) :
  xs ⨁ (ΔList.del i n : ΔList α Δα) =
    let (xs₁, xs₂) := List.splitAt i xs
    xs₁ ++ xs₂.drop n := by simp [Change.patch]
@[simp] theorem ListChange.patch_upd {α Δα : Type} [Change α Δα]
  (xs : List α) (i : Nat) (ds : List Δα) :
  xs ⨁ (ΔList.upd i ds : ΔList α Δα) =
    let (xs₁, xs₂) := List.splitAt i xs
    let (ys, zs) := List.splitAt ds.length xs₂
    xs₁ ++ ys.zipWith Change.patch ds ++ zs := by simp [Change.patch]


@[simp] def asDeltaNat : ΔList α Δα → ΔNat
  | .ins _ l => .inc l.length
  | .del _ n => .dec n
  | .upd _ _ => .inc 0

@[simp] def length : ΔList α Δα → Nat
  | .ins _ l => l.length
  | .del _ n => n
  | .upd _ Δxs => Δxs.length

@[simp] def getPos : ΔList α Δα → Nat
  | .ins i _ => i
  | .del i _ => i
  | .upd i _ => i

@[simp] def setPos (k : Nat) : ΔList α Δα → ΔList α Δα
  | .ins _ l => .ins k l
  | .del _ n => .del k n
  | .upd _ l => .upd k l

@[simp] def changePosWith (f : Nat → Nat) : ΔList α Δα → ΔList α Δα
  | .ins i l => .ins (f i) l
  | .del i n => .del (f i) n
  | .upd i l => .upd (f i) l
end ΔList
