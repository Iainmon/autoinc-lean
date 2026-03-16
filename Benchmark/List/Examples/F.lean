import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.Experiment
import Benchmark.List.Random
import AssertCmd


namespace Example6
/- reverse -> reverse -/

open StructProd2

abbrev Env := T Nat Nat

abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)

def reverse_op_0 := Operator.zoomStateT _ reverse_op (Lens₀ : Lens Env Nat)
def reverse_op_1 := Operator.zoomStateT _ reverse_op (Lens₁ : Lens Env Nat)


def op := reverse_op_0 >>>> reverse_op_1



namespace Benchmark

abbrev A := List Nat
abbrev B := List Nat
abbrev ΔA := ΔList Nat ΔNat
abbrev ΔB := ΔList Nat ΔNat


abbrev input := List.range 10000


instance : SizeOf A where
  sizeOf _ := 10000
def case_1 : Case A B ΔA ΔB Env where
  op := op
  id := 1
  description := "insertion in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 5000 size g |> Prod.fst

def case_2 : Case A B ΔA ΔB Env where
  op := op
  id := 2
  description := "insertion in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 5001 9999 size g |> Prod.fst

def case_3 : Case A B ΔA ΔB Env where
  op := op
  id := 3
  description := "deletion in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 5000 size g |> Prod.fst

def case_4 : Case A B ΔA ΔB Env where
  op := op
  id := 4
  description := "deletion in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 5001 9999 size g |> Prod.fst

def case_5 : Case A B ΔA ΔB Env where
  op := op
  id := 5
  description := "update in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 5000 size g |> Prod.fst

def case_6 : Case A B ΔA ΔB Env where
  op := op
  id := 6
  description := "update in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 5001 9999 size g |> Prod.fst

def cases := [case_1, case_2, case_3, case_4, case_5, case_6]



end Benchmark



end Example6
