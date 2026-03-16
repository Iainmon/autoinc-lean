import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.ExperimentReaderT
import Benchmark.List.Random
import AssertCmd
open ExperimentReaderT
namespace Example9
/- drop -> reverse -> drop -> reverse -> all -/
/-
    digraph G {
      node [shape=box, fixedsize=true, width=1, height=1];
      input_0_nat [shape=none];
      input_1_list [shape=none];
      input_2_nat [shape=none];

      input_0_nat -> drop_0;
      input_1_list -> drop_0;
      drop_0 -> reverse_0;
      reverse_0 -> drop_1;
      input_2_nat -> drop_1;
      drop_1 -> reverse_1;
      reverse_1 -> all;
    }
-/
open StructProd5

abbrev drop_op :=
  ΔList.Drop.op (α:=Nat) (Δα:=ΔNat) (LazyEagerStateT (List Nat) (Nat × Nat) (ReaderT (Nat → Bool) IO))
abbrev drop_partial_op := ΔList.Drop.partial_op (α:=Nat) (Δα:=ΔNat) (LazyEagerStateT (List Nat) (Nat × Nat) (ReaderT (Nat → Bool) IO))

abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat (ReaderT (Nat → Bool) IO))
abbrev all_op := ΔList.All.op (α:=Nat) (Δα:=ΔNat) (LazyEagerStateT (List Nat) Bool (ReaderT (Nat → Bool) IO))

abbrev Drop_0_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev Reverse_0_ST := Nat
abbrev Drop_1_ST := LazyEagerState (List Nat) (Nat × Nat)
abbrev Reverse_1_ST := Nat
abbrev All_0_ST := LazyEagerState (List Nat) Bool


abbrev Env := T
    Drop_0_ST
    Reverse_0_ST
    Drop_1_ST
    Reverse_1_ST
    All_0_ST


variable (pred : Nat → Bool)


/- Insert an element at index 0 -/
def drop_0 := Operator.zoomStateT (ReaderT (Nat → Bool) IO) drop_op (Lens₀ : Lens Env _)
def reverse_0 := Operator.zoomStateT (ReaderT (Nat → Bool) IO) reverse_op (Lens₁ : Lens Env _) |> Operator.toSeq
def drop_1 := PartialOperator.zoomStateT (ReaderT (Nat → Bool) IO) drop_partial_op (Lens₂ : Lens Env _) |> PartialOperator.toSeq₁ |> PartialOperator.toOperator
def reverse_1 := Operator.zoomStateT (ReaderT (Nat → Bool) IO) reverse_op (Lens₃ : Lens Env _) |> Operator.toSeq
def all := Operator.zoomStateT (ReaderT (Nat → Bool) IO) (all_op) (Lens₄ : Lens Env _) |> Operator.toSeq

def op :=
       drop_0
  >>>> reverse_0
  >>>>₁ drop_1
  >>>> Flatten.op
  >>>> reverse_1
  >>>> all


namespace Benchmark

abbrev A := (List Nat × Nat) × Nat
abbrev B := Bool
abbrev ΔA := (ΔProd (ΔProd (ΔList Nat ΔNat) ΔNat) ΔNat)
abbrev ΔB := List ΔBool


abbrev input₁ := List.range 9000
abbrev input₂ := 3000
abbrev input₃ := 3000

instance : SizeOf A where
  sizeOf _ := 9000
-- (fun x => x > 2500 && x < 6500)
def case_1 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 1
  description := "insert elements before the drop point (all true)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 3000 size g |> (·.1) |> ΔProd.first_1
-- (fun x => x > 2500 && x < 6500)
def case_2 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 2
  description := "delete elements before the drop point (all true)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 3000 size g |> (·.1) |> ΔProd.first_1
-- (fun x => x % 2 = 0)
def case_3 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 3
  description := "insert elements before the drop point (all false)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 3000 size g |> (·.1) |> ΔProd.first_1
-- (fun x => x % 2 = 0)
def case_4 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 4
  description := "delete elements before the drop point (all false)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 3000 size g |> (·.1) |> ΔProd.first_1
-- (fun x => x > 2500 && x < 6500)
def case_5 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 5
  description := "increase the drop_0 point (all true)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange _ _ := ΔNat.inc 30 |> ΔProd.first_2
-- (fun x => x > 2500 && x < 6500)
def case_6 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 6
  description := "decrease the drop_0 point (all true)"
  rep := 5
  input := ((input₁, input₂), input₃)
  p := 5
  genChange _ _ := ΔNat.dec 30 |> ΔProd.first_2
-- (fun x => x % 2 = 0)
def case_7 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 7
  description := "increase the drop_1 point (all false)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange _ _ := ΔNat.inc 30 |> ΔProd._2
-- (fun x => x % 2 = 0)
def case_8 : Case A B ΔA ΔB Env (Nat → Bool) where
  op := op
  id := 8
  description := "decrease the drop_1 point (all false)"
  rep := 100
  input := ((input₁, input₂), input₃)
  p := 5
  genChange _ _ := ΔNat.dec 30 |> ΔProd._2

def cases_1 :=
  (fun x => (x > 2500 && x < 6500 : Bool), [
    case_1, case_2, case_5, case_6
  ])

def cases_2 :=
  (
    fun x => (x %2 == 0 : Bool),
    [
      case_3, case_4, case_7, case_8
    ],
  )


def cases := [case_1, case_2, case_3, case_4, case_5, case_6, case_7, case_8]


end Benchmark


end Example9
