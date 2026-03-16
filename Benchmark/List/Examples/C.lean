import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Autoinc.Data.List.Operator
import Benchmark.ExperimentReaderT
import Benchmark.List.Random
import AssertCmd
open ExperimentReaderT
namespace Example3
/- drop -> take -> all -/

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
  take -> all;
}
-/
open StructProd3
abbrev Drop_0_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev Take_0_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev All_0_ST := LazyEagerState (List Nat) Bool
abbrev Env := T
  Drop_0_ST -- Drop
  Take_0_ST -- Take
  All_0_ST  -- All


abbrev drop_op := ΔList.Drop.op (α:=Nat) (Δα:=ΔNat)
abbrev take_op := ΔList.Take.partial_op (α:=Nat) (Δα:=ΔNat)
abbrev all_op := ΔList.All.op (α:=Nat) (Δα:=ΔNat)
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



def all_0 :=
  Operator.zoomStateT _
    (all_op (LazyEagerStateT (List Nat) Bool (ReaderT (Nat → Bool) IO)))
    (Lens₂ : Lens Env All_0_ST)
  |> Operator.toSeq





-- def take :=
--    ΔList.Take.partial_op (α:=Nat) (Δα:=ΔNat) StackTake |>
--    PartialOperator.toSeq₁ |>
--    PartialOperator.toOperator |>
--    Operator.lift (n:=StackDrop)


-- def all :=
--   ΔList.All.op (α:=Nat) (Δα:=ΔNat) StackAll p |>
--   Operator.lift (n:=StackTake) |>
--   Operator.lift (n:=StackDrop) |>
--   Operator.toSeq


def op := drop_0 >>>>₁ take_0 >>>> Flatten.op >>>> Flatten.op >>>> all_0

namespace Benchmark

abbrev A := (List Nat × Nat) × Nat
abbrev B := Bool
abbrev ΔA := (ΔProd (ΔProd (ΔList Nat ΔNat) ΔNat) ΔNat)
abbrev ΔB := (List (ΔBool))

abbrev input₁ := List.range 9000
abbrev input₂ := 3000
abbrev input₃ := 3000
abbrev input := ((input₁, input₂), input₃)

instance : SizeOf A where
  sizeOf _ := 9000
def buildCase (id : Nat) (description : String) (genChange : StdGen → Nat → ΔA) (pred : Nat → Bool) (rep:Nat:=100) : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := id
  description := description
  rep := rep
  input := input
  p := 5
  genChange := genChange

/-
Optimal case:
- Drop : insertion after the drop point; deletion
- Take : insertion / deletion after the take point
- All  : insertion / deletion when the predicate is `true` on all elements
-/

/-
Case 1: insert elements inside the list being taken,
`all` always returns true
-/


def case_1 :=
  buildCase
    1
    "insert elements inside the list being taken (all true)"
    (fun g size => randIns 3001 4000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)

/-
Case 2 and 3: delete elements outside the list being taken,
`all` always returns true
-/


def case_2 :=
  buildCase
    2
    "delete elements outside the list being taken (all true)"
    (fun g size => randDel 7000 8000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)


def case_3 :=
  buildCase
    3
    "delete elements outside the list being taken (all true)"
    (fun g size => randDel 1000 2000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)


/-
Case 4 and 5: insert elements outside the list being taken,
`all` always returns true
-/


def case_4 :=
  buildCase
    4
    "insert elements outside the list being taken (all true)"
    (fun g size => randIns 7000 8000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)

def case_5 :=
  buildCase
    5
    "insert elements outside the list being taken (all true)"
    (fun g size => randIns 1001 2000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)


/-
Case 6: delete elements inside the list being taken,
`all` always returns true
-/


def case_6 :=
  buildCase
    6
    "delete elements inside the list being taken (all true)"
    (fun g size => randDel 3001 4000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x > 1000)



/-
Case 7: insert elements inside the list being taken,
`all` returns false
-/


def case_7 :=
  buildCase
    7
    "insert elements inside the list being taken"
    (fun g size => randIns 3001 4000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)

/-
Case 8 and 9: delete elements outside the list being taken,
`all` returns false
-/


def case_8 :=
  buildCase
    8
    "delete elements outside the list being taken "
    (fun g size => randDel 7000 8000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)


def case_9 :=
  buildCase
    9
    "delete elements outside the list being taken "
    (fun g size => randDel 1000 2000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)


/-
Case 10 and 11: insert elements outside the list being taken,
`all` always returns true
-/


def case_10 :=
  buildCase
    4
    "insert elements outside the list being taken"
    (fun g size => randIns 7000 8000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)

def case_11 :=
  buildCase
    11
    "insert elements outside the list being taken (all true)"
    (fun g size => randIns 1001 2000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)


/-
Case 6: delete elements inside the list being taken,
`all` always returns true
-/


def case_12 :=
  buildCase
    12
    "delete elements inside the list being taken (all true)"
    (fun g size => randDel 3001 4000 size g |> (·.1) |> ΔProd.first_1)
    (fun x => x % 2 == 0)




-- def case_3 :=
--   buildCase
--     3
--     "insert elements before the drop point (all false)"
--     (fun g size => randIns 0 3000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x % 2 = 0)

-- def case_4 :=
--   buildCase
--     4
--     "delete elements before the drop point (all false)"
--     (fun g size => randDel 0 3000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x % 2 = 0)

-- def case_5 :=
--   buildCase
--     5
--     "increase the drop point (all true)"
--     (fun _ _ => ΔNat.inc 30 |> ΔProd.first_2)
--     (fun x => x > 1000)

-- def case_6 :=
--   buildCase
--     6
--     "decrease the drop point (all true)"
--     (fun _ _ => ΔNat.dec 30 |> ΔProd.first_2)
--     (fun x => x > 1000)

-- def case_7 :=
--   buildCase
--     7
--     "increase the drop point (all false)"
--     (fun _ _ => ΔNat.inc 30 |> ΔProd.first_2)
--     (fun x => x % 2 = 0)

-- def case_8 :=
--   buildCase
--     8
--     "decrease the drop point (all false)"
--     (fun _ _ => ΔNat.dec 30 |> ΔProd.first_2)
--     (fun x => x % 2 = 0)

-- def case_9 :=
--   buildCase
--     9
--     "insert elements after the drop point (all true)"
--     (fun g size => randIns 6000 8000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x > 1000)

-- def case_10 :=
--   buildCase
--     10
--     "delete elements after the drop point (all true)"
--     (fun g size => randDel 6000 8000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x > 1000)

-- def case_11 :=
--   buildCase
--     11
--     "insert elements after the drop point (all false)"
--     (fun g size => randIns 6000 8000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x % 2 = 0)

-- def case_12 :=
--   buildCase
--     12
--     "delete elements after the drop point (all false)"
--     (fun g size => randDel 6000 8000 size g |> (·.1) |> ΔProd.first_1)
--     (fun x => x % 2 = 0)


def cases_1 :=
  (fun x => (x > 1000 : Bool), [
    case_1,
    case_2,
    case_3,
    case_4,
    case_5,
    case_6,
  ])
def cases_2 :=
  ((fun x => (x % 2 == 0 : Bool)), [
    case_7,
    case_8,
    case_9,
    case_10,
    case_11,
    case_12
  ])

def cases :=
  [
    case_1,
    case_2,
    case_3,
    case_4,
    case_5,
    case_6,
    case_7,
    case_8,
    case_9,
    case_10,
    case_11,
    case_12
  ]



end Benchmark





end Example3
