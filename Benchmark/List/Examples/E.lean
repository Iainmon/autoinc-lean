/- Some change generators may generate invalid changes -/
import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Experiment
import Benchmark.List.Random
import Benchmark.Utils
import AssertCmd

namespace Example5
/- reverse -> length -/

abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)
abbrev length_op := ΔList.Length.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)



def op := reverse_op >>>> length_op



namespace Benchmark

abbrev A := List Nat
abbrev B := Nat
abbrev ΔA := ΔList Nat ΔNat
abbrev ΔB := ΔNat

abbrev input := List.range 10000

instance : SizeOf A where
  sizeOf _ := 10000

def case_1 : Case A B ΔA ΔB Nat where
  op := op
  id := 1
  description := "insertion in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 5000 size g |> Prod.fst

def case_2 : Case A B ΔA ΔB Nat where
  op := op
  id := 2
  description := "insertion in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 5001 9999 size g |> Prod.fst

def case_3 : Case A B ΔA ΔB Nat where
  op := op
  id := 3
  description := "deletion in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 5000 size g |> Prod.fst

def case_4 : Case A B ΔA ΔB Nat where
  op := op
  id := 4
  description := "deletion in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 5001 9999 size g |> Prod.fst

def case_5 : Case A B ΔA ΔB Nat where
  op := op
  id := 5
  description := "update in the first half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 5000 size g |> Prod.fst

def case_6 : Case A B ΔA ΔB Nat where
  op := op
  id := 6
  description := "update in the second half of the list"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 5001 6000 size g |> Prod.fst

def cases := [
    case_1,
    case_2,
    case_3,
    case_4,
    case_5,
    case_6
  ]



end Benchmark


end Example5
