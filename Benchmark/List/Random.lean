import Autoinc.Data.List.Change



section
variable {g : Type} [RandomGen g]
/-- Generate a list of `n` random Nats between `lo` and `hi` -/
def randNatList (n : Nat) (lo hi : Nat) (gen : g) : List Nat × g :=
  match n with
  | 0 => ([], gen)
  | k + 1 =>
    let (val, gen') := randNat gen lo hi   -- 1. Generate one value
    let (rest, finalGen) := randNatList k lo hi gen' -- 2. Pass *new* gen to recursive call
    (val :: rest, finalGen)

/- Generate random insertion changes. -/
def randIns
  (lo hi : Nat) -- range of the position
  (size : Nat) -- size of the inserted sublist
  (gen : g)
  : ΔList Nat ΔNat × g :=
  let (pos, gen') := randNat gen lo hi
  let (xs, finalGen) := randNatList size 0 1000 gen'
  (ΔList.ins pos xs, finalGen)

/- Generate random deletion changes. -/
def randDel
  (lo hi : Nat) -- range of the position
  (size : Nat) -- size of the deleted sublist
  (gen : g)
  : ΔList Nat ΔNat × g :=
  let (pos, finalGen) := randNat gen lo hi
  (ΔList.del pos size, finalGen)
/- 50% chance for insertion, 50% chance for deletion -/
def randInsDel
  (lo hi : Nat)
  (size : Nat)
  (gen : g)
  : ΔList Nat ΔNat × g :=
  -- Generate a random number between 0 and 1
  let (coin, gen') := randNat gen 0 1
  if coin == 0 then
    randIns lo hi size gen'
  else
    randDel lo hi size gen'
/- Generate random inc change. -/
def randInc
  (lo hi : Nat)
  (gen : g) : ΔNat × g :=
  let (n, finalGen) := randNat gen lo hi
  (ΔNat.inc n, finalGen)

/- Generate random dec change. -/
def randDec
  (lo hi : Nat)
  (gen : g) : ΔNat × g :=
  let (n, finalGen) := randNat gen lo hi
  (ΔNat.dec n, finalGen)

/-
Generate random update changes.
(due to validity, we only generate inc changes)
-/
def randUpd
  (lo hi : Nat) -- range of the position
  (size : Nat) -- size of the updated sublist
  (gen : g)
  : ΔList Nat ΔNat × g :=
  let (pos, gen') := randNat gen lo hi
  let (xs, finalGen) := randNatList size 0 1000 gen'
  (ΔList.upd pos $ xs.map ΔNat.inc, finalGen)

end
