import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.Utils
import Benchmark.Experiment
import Benchmark.List.Random
import Benchmark.List.Operators
import AssertCmd


namespace Example2
/- append -> append -> length -/


/-
digraph G {
  append_0 -> append_1;
  append_1 -> flatten;
  flatten -> length;
  input_0 -> append_0;
  input_1 -> append_0;
  input_2 -> append_1;

  node [shape=square];
  input_0 [shape=none];
  input_1 [shape=none];
  input_2 [shape=none];
}

-/
open StructProd2

abbrev Env := T Nat Nat

abbrev append_op := ΔList.Append.op (α:=Nat) (Δα:=ΔNat)
abbrev append_partial_op := ΔList.Append.partial_op (α:=Nat) (Δα:=ΔNat)
abbrev length_op :=
  ΔList.Length.op (α:=Nat) (Δα:=ΔNat) (StateT (T Nat Nat) IO)
  |> Operator.toSeq





def append_0 :=
  Operator.zoomStateT _ (append_op (StateT Nat IO)) (Lens₀ : Lens Env Nat)
def append_1 :=
  PartialOperator.zoomStateT _
    (append_partial_op (StateT Nat IO)) (Lens₁ : Lens Env Nat)
  |> PartialOperator.toSeq₁
  |> PartialOperator.toOperator


def op :=
        append_0
  >>>>₁ append_1
  >>>>  Flatten.op
  >>>>  length_op
  >>>>  ΔNat.Compression.op


namespace Benchmark

/-
Type of changes:
1. Insert / Delete / Update on the first operand to `append_0` ( O(1) )
2. Insert / Delete / Update on the second operand to `append_0` ( O(1) )
3. Insert / Delete / Update on the second operand to `append_1` ( O(1) )
-/

abbrev input₁ := List.range 10000
abbrev input₂ := List.range' 10001 20000
abbrev input₃ := List.range' 20001 30000

abbrev input := ((input₁, input₂), input₃)

abbrev A := ((List Nat × List Nat) × List Nat)
abbrev B := Nat
abbrev ΔA := (ΔProd (ΔProd (ΔList Nat ΔNat) (ΔList Nat ΔNat)) (ΔList Nat ΔNat))
abbrev ΔB := ΔNat

instance : SizeOf A where
  sizeOf _ := 10000


def case_1 : Case A B ΔA ΔB Env where
  op := op
  id := 1
  description := "insertion in the first operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 10000 size g |> Prod.fst |> ΔProd.first_1

def case_2 : Case A B ΔA ΔB Env where
  op := op
  id := 2
  description := "deletion in the first operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 10000 size g |> Prod.fst |> ΔProd.first_1

def case_3 : Case A B ΔA ΔB Env where
  op := op
  id := 3
  description := "updating in the first operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 10000 size g |> Prod.fst |> ΔProd.first_1

def case_4 : Case A B ΔA ΔB Env where
  op := op
  id := 4
  description := "insertion in the second operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 10000 size g |> Prod.fst |> ΔProd.first_2

def case_5 : Case A B ΔA ΔB Env where
  op := op
  id := 5
  description := "deletion in the second operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 10000 size g |> Prod.fst |> ΔProd.first_2

def case_6 : Case A B ΔA ΔB Env where
  op := op
  id := 6
  description := "updating in the second operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 10000 size g |> Prod.fst |> ΔProd.first_2

def case_7 : Case A B ΔA ΔB Env where
  op := op
  id := 7
  description := "insertion in the second operand of append_1"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 10000 size g |> Prod.fst |> ΔProd._2

def case_8 : Case A B ΔA ΔB Env where
  op := op
  id := 8
  description := "deletion in the second operand of append_1"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 10000 size g |> Prod.fst |> ΔProd._2

def case_9 : Case A B ΔA ΔB Env where
  op := op
  id := 9
  description := "updating in the second operand of append_1"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 10000 size g |> Prod.fst |> ΔProd._2


def cases := [case_1, case_2, case_3, case_4, case_5, case_6, case_7, case_8, case_9]


end Benchmark


end Example2
