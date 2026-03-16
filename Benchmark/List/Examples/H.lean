import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.Experiment
import Benchmark.List.Random
import AssertCmd



namespace Example8
/- append -> cons -> tail -> reverse -> length -/
/-
digraph G {
  node [shape=box, fixedsize=true, width=1, height=1];
  input_0_list [shape=none];
  input_1_list [shape=none];
  input_2_nat [shape=none];

  input_0_list -> append;
  input_1_list -> append;
  append -> cons;
  input_2_nat -> cons;
  cons -> tail;
  tail -> reverse;
  reverse -> length;
}
-/
open StructProd3




abbrev Append_0_ST  := Nat
abbrev Tail_0_ST    := Thunk (List Nat)
abbrev Reverse_0_ST := Nat


abbrev Env := T
    Append_0_ST      /- append -/
    Tail_0_ST        /- tail -/
    Reverse_0_ST     /- reverse -/


abbrev append_op := ΔList.Append.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)
abbrev tail_op := ΔList.Tail.op (α:=Nat) (Δα:=ΔNat) (LazyStateT (List Nat) IO)
abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)


def append_0 := Operator.zoomStateT IO append_op (Lens₀ : Lens Env Nat)
def tail_0 := Operator.zoomStateT IO tail_op (Lens₁ : Lens Env _)
def reverse_0 := Operator.zoomStateT IO reverse_op (Lens₂ : Lens Env _)


def op :=
       append_0
  >>>>₂ (ΔList.Cons.partial_op _).toSeq₂.toOperator
  >>>> Flatten.op
  >>>> tail_0.toSeq
  >>>> reverse_0.toSeq


namespace Benchmark

abbrev A := (List Nat × List Nat) × Nat
abbrev B := List Nat
abbrev ΔA := (ΔProd (ΔProd (ΔList Nat ΔNat) (ΔList Nat ΔNat)) ΔNat)
abbrev ΔB := (List (ΔList Nat ΔNat))


abbrev input₁ := List.range 10000
abbrev input₂ := List.range' 10001 20000
abbrev input₃ := 1

instance : SizeOf A where
  sizeOf _ := 10000

abbrev input := ((input₁, input₂), input₃)

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
  id := 5
  description := "updating in the second operand of append_0"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 10000 size g |> Prod.fst |> ΔProd.first_2

def case_7 : Case A B ΔA ΔB Env where
  op := op
  id := 7
  description := "increase the second operand of cons"
  rep := 100
  input := input
  p := 5
  genChange _ _ := ΔNat.inc 10 |> ΔProd._2


def case_8 : Case A B ΔA ΔB Env where
  op := op
  id := 7
  description := "decrease the second operand of cons"
  rep := 100
  input := input
  p := 5
  genChange _ _ := ΔNat.dec 10 |> ΔProd._2

def cases := [case_1, case_2, case_3, case_4, case_5, case_6, case_7, case_8]




end Benchmark


end Example8
