import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.ExperimentReaderT
import Benchmark.List.Random
import AssertCmd
open ExperimentReaderT

namespace Example4
/- drop -> take -> any -/

/-
digraph G {
  node [shape=box, fixedsize=true, width=1, height=1];
  input_0_nat [shape=none];
  input_1_list [shape=none];
  input_2_nat [shape=none];

  input_0_nat -> drop;
  input_1_list -> drop;
  input_2_nat -> take;
  drop -> take;
  take -> any;
}
-/
variable (p : Nat → Bool)

open StructProd3

abbrev Drop_0_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev Take_0_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev Any_0_ST := LazyEagerState (List Nat) Bool
abbrev Env := T
  Drop_0_ST -- Drop
  Take_0_ST -- Take
  Any_0_ST  -- Any

abbrev drop_op := ΔList.Drop.op (α:=Nat) (Δα:=ΔNat)
abbrev take_op := ΔList.Take.partial_op (α:=Nat) (Δα:=ΔNat)
abbrev any_op := ΔList.Any.op (α:=Nat) (Δα:=ΔNat)

def drop_0 :=
  Operator.zoomStateT _
    (drop_op (LazyEagerStateT (List Nat) (Nat × Nat) (ReaderT (Nat → Bool) IO)))
    (Lens₀ : Lens Env Drop_0_ST)

def take_0 :=
  PartialOperator.zoomStateT _
    (take_op (LazyEagerStateT (List Nat) (Nat × Nat) (ReaderT (Nat → Bool) IO)))
    (Lens₁ : Lens Env Take_0_ST)
  |> PartialOperator.toSeq₁
  |> PartialOperator.toOperator

def any_0 :=
  Operator.zoomStateT _
    (any_op (LazyEagerStateT (List Nat) Bool (ReaderT (Nat → Bool) IO)))
    (Lens₂ : Lens Env Any_0_ST)
  |> Operator.toSeq


def op := drop_0 >>>>₁ take_0 >>>> Flatten.op >>>> Flatten.op >>>> any_0



namespace Benchmark

abbrev A := (List Nat × Nat) × Nat
abbrev B := Bool
abbrev ΔA := (ΔProd (ΔProd (ΔList Nat ΔNat) ΔNat) ΔNat)
abbrev ΔB := List ΔBool







abbrev input₁ := List.range 9000
abbrev input₂ := 3000
abbrev input₃ := 3000
abbrev input := ((input₁, input₂), input₃)

instance : SizeOf A where
  sizeOf _ := 9000

/-
Case 0: insert / delete elements after the list being taken,
(drop : efficient, take : efficient, any: efficient (no change))
-/
-- (fun x => x > 10000)
def case_0 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 0
  description := "insert / delete elements after the list being taken (any:false)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randInsDel 6000 7000 size g |> (·.1) |> ΔProd.first_1

/-
Case 1: insert elements inside the list being taken,
`any` always returns false
drop: efficient, take: efficient, any: efficient
-/
-- (fun x => x > 10000)
def case_1 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 1
  description := "insert elements inside the list being taken (any:false)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 4000 5000 size g |> (·.1) |> ΔProd.first_1



/-
Case 2: insert elements inside the list being taken,
`any` returns true in the initial run
drop: efficient, take: efficient, any: inefficient
-/
-- (fun x => x ≥ 0)
def case_2 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 2
  description := "insert elements inside the list being taken (any:true)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 4000 5000 size g |> (·.1) |> ΔProd.first_1

/-
Case 3: delete elements inside the list being taken,
`any` always returns false
drop: efficient, take: inefficient, any: efficient
-/
-- (fun x => x > 10000)
def case_3 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 3
  description := "delete elements inside the list being taken (any:false)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 4000 5000 size g |> (·.1) |> ΔProd.first_1


/-
Case 4: delete elements inside the list being taken,
`any` returns true
drop: efficient, take: inefficient, any: inefficient
-/
-- (fun x => x ≥ 0)
def case_4 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 4
  description := "delete elements inside the list being taken (any:true)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 4000 5000 size g |> (·.1) |> ΔProd.first_1

/-
Case 5: insert elements before the list being taken,
`any` always returns false
drop: inefficient, take: efficient, any: efficient
-/
-- (fun x => x > 10000)
def case_5 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 1
  description := "insert elements inside the list being taken (any:false)"
  rep := 50
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 1000 2000 size g |> (·.1) |> ΔProd.first_1



-- /-
-- Case 3: insert elements inside the list being taken,
-- `any` initially returns true
-- drop: efficient, take: efficient, any: inefficient
-- -/

-- def case_2 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 1
--   description := "insert elements inside the list being taken,
-- `any` always returns false"
--   rep := 50
--   input := input
--   p := 5
--   genChange (g : StdGen) (size : Nat) :=
--     randIns 4000 5000 size g |> (·.1) |> ΔProd.first_1

-- /-
-- Case 3: delete elements after the list being taken,
-- the predicate always returns true
-- (not efficient,)
-- -/

-- def case_3 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 0)
--   id := 3
--   description := "delete elements after the list being taken (optima)"
--   rep := 50
--   input := input
--   p := 5
--   genChange (g : StdGen) (size : Nat) :=
--     randDel 6000 7000 size g |> (·.1) |> ΔProd.first_1




-- /- Case 1 : insert elements before the drop point
-- Slow because it will trigger deletion in the take operator
-- -/
-- def case_1 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 1
--   description := "insert elements before the drop point (any true)"
--   rep := 100
--   input := input
--   p := 1
--   genChange (g : StdGen) (size : Nat) :=
--     randIns 0 3000 size g |> (·.1) |> ΔProd.first_1

-- /- Case 2 : delete elements before the drop point with a predicate that always returns true -/
-- def case_2 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 1000)
--   id := 2
--   description := "delete elements before the drop point (any true)"
--   rep := 100
--   input := input
--   p := 1
--   genChange (g : StdGen) (size : Nat) :=
--     randDel 0 3000 size g |> (·.1) |> ΔProd.first_1

-- /- Case 3 : insert elements before the drop point with a predicate that always returns false -/
-- def case_3 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 3
--   description := "insert elements before the drop point (any false)"
--   rep := 100
--   input := input
--   p := 5
--   genChange (g : StdGen) (size : Nat) :=
--     randIns 0 3000 size g |> (·.1) |> ΔProd.first_1

-- /- Case 4 : delete elements before the drop point with a predicate that always returns false -/
-- def case_4 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 4
--   description := "delete elements before the drop point (any false)"
--   rep := 100
--   input := input
--   p := 5
--   genChange (g : StdGen) (size : Nat) :=
--     randDel 0 3000 size g |> (·.1) |> ΔProd.first_1

-- /- Case 5 : increase the drop point (any true) -/
-- def case_5 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 1000)
--   id := 5
--   description := "increase the drop point (any true)"
--   rep := 100
--   input := input
--   p := 5
--   genChange _ _ := ΔNat.inc 30 |> ΔProd.first_2

-- /- Case 6 : decrease the drop point (any true) -/
-- def case_6 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 1000)
--   id := 6
--   description := "decrease the drop point (any true)"
--   rep := 100
--   input := input
--   p := 5
--   genChange _ _ := ΔNat.dec 30 |> ΔProd.first_2

-- /- Case 7 : increase the drop point (any false) -/
-- def case_7 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 7
--   description := "increase the drop point (any true)"
--   rep := 100
--   input := input
--   p := 5
--   genChange _ _ := ΔNat.inc 30 |> ΔProd.first_2

-- /- Case 8 : decrease the drop point (any false) -/
-- def case_8 : Case A B ΔA ΔB Env where
--   op := op (fun x => x > 10000)
--   id := 8
--   description := "decrease the drop point (any false)"
--   rep := 100
--   input := input
--   p := 5
--   genChange _ _ := ΔNat.dec 30 |> ΔProd.first_2

-- (fun x => x > 10000)
def cases_1 :=
(fun x => (x > 10000 : Bool), [
  case_0, case_1, case_3, case_5
])

-- (fun x => x ≥ 0)
def cases_2 := (fun x => (x ≥ 0 : Bool), [case_2])


def cases := [
    case_0,
    case_1,
    case_2,
    case_3,
    case_4,
    case_5,
    -- case_6,
    -- case_7,
    -- case_8
  ]




end Benchmark



end Example4
