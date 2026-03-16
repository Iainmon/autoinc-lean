import Autoinc.Change

/-- change representation for Nat -/
inductive ΔNat : Type where
  | inc : Nat → ΔNat
  | dec : Nat → ΔNat
deriving Repr, BEq

instance : ToString ΔNat where
  toString | ΔNat.inc n => s!"inc {n}"
           | ΔNat.dec n => s!"dec {n}"

/-- change class for Nat -/
instance NatChange : Change Nat ΔNat where
  patch n d := match d with
  | ΔNat.inc m => n + m
  | ΔNat.dec m => n - m
  valid n d := match d with
  | ΔNat.inc _ => True
  | ΔNat.dec m => n ≥ m

@[simp, grind] theorem NatChange.valid_inc (n dn : Nat) : n ⊢ ΔNat.inc dn := by simp [Change.valid]
@[simp, grind] theorem NatChange.valid_dec {n dn : Nat} : n ≥ dn → n ⊢ ΔNat.dec dn := by simp_all [Change.valid]
@[grind] theorem NatChange.valid_dec_elim {n dn : Nat} : n ⊢ ΔNat.dec dn → n ≥ dn := by simp_all [Change.valid]
@[simp, grind] theorem NatChange.patch_inc (n dn : Nat) : Change.patch n (ΔNat.inc dn) = n + dn := rfl
@[simp, grind] theorem NatChange.patch_dec (n dn : Nat) : Change.patch n (ΔNat.dec dn) = n - dn := rfl

@[simp] def NatChange.concat (d1 d2 : ΔNat) : ΔNat :=
  match d1, d2 with
  | ΔNat.inc m1, ΔNat.inc m2 => ΔNat.inc (m1 + m2)
  | ΔNat.dec m1, ΔNat.dec m2 => ΔNat.dec (m1 + m2)
  | ΔNat.inc m, ΔNat.dec n => if m ≥ n then ΔNat.inc (m - n) else ΔNat.dec (n - m)
  | ΔNat.dec n, ΔNat.inc m => if n ≥ m then ΔNat.dec (n - m) else ΔNat.inc (m - n)

infixl:70 " <++> " => NatChange.concat

theorem NatChange.concat_valid (old new : ΔNat) (n : Nat) :
  n ⊢ old → n ⨁ old ⊢ new → n ⊢ old <++> new := by
  intros h1 h2
  cases old <;> cases new <;> simp_all [Change.valid] <;> grind

@[simp] def nat_diff (new old : Nat) : ΔNat :=
  if old < new then ΔNat.inc (new - old)
  else ΔNat.dec (old - new)

instance NatDifference : Difference Nat ΔNat where
  diff new old := nat_diff new old
  diff_valid new old := by
    cases new <;> cases old <;> simp [nat_diff, Change.valid] <;> grind
  diff_correct new old := by
    cases new <;> cases old <;> simp [nat_diff, Change.patch] <;> grind

@[simp] def NatChange.invert : ΔNat → ΔNat
  | ΔNat.inc n => ΔNat.dec n
  | ΔNat.dec n => ΔNat.inc n
instance : ChangeInversion Nat ΔNat where
  invert := NatChange.invert
  valid_invert : ∀ (t : Nat) (Δt : ΔNat),
    t ⊢ Δt → t ⨁ Δt ⊢ NatChange.invert Δt := by
    intros t Δt hv ; cases Δt <;> cases hv <;> simp at *
  correct_invert : ∀ (t : Nat) (Δt : ΔNat),
    t ⊢ Δt → t ⨁ Δt ⨁ NatChange.invert Δt = t := by
    intros t Δt hv ; cases Δt <;> cases hv <;> simp at * ; omega
