import Autoinc.Combinator
import Autoinc.Data.List.Operator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.Experiment
import Benchmark.List.Random
import AssertCmd

namespace Example7
/- reverse -> tail -> cons -> reverse -> head -/
/-
digraph G {
  node [shape=box, fixedsize=true, width=1, height=1];
  input_1_list [shape=none];
  input_2_nat [shape=none];
  output_1_option_nat [shape=none];

  input_1_list -> reverse_0;
  reverse_0 -> tail;
  tail -> cons;
  input_2_nat -> cons;
  cons -> reverse;
  reverse -> head;
  head -> output_1_option_nat;
}
-/


open StructProd4

abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)
abbrev tail_op := ΔList.Tail.op (α:=Nat) (Δα:=ΔNat) (LazyStateT (List Nat) IO)
abbrev head_op := ΔList.Head.op (α:=Nat) (Δα:=ΔNat) (LazyStateT (List Nat) IO)


abbrev Reverse_0_ST := Nat
abbrev Reverse_1_ST := Nat
abbrev Tail_0_ST := Thunk (List Nat)
abbrev Head_0_ST := Thunk (List Nat)





abbrev Env := T
    Reverse_0_ST      /- reverse -/
    Tail_0_ST         /- tail -/
    Reverse_0_ST      /- reverse -/
    Head_0_ST         /- head -/




abbrev reverse_op_0 := Operator.zoomStateT _ reverse_op (Lens₀ : Lens Env Nat)
abbrev tail_op_0 := Operator.zoomStateT _ tail_op (Lens₁ : Lens Env _)
abbrev reverse_op_1 := Operator.zoomStateT _ reverse_op (Lens₂ : Lens Env Nat)
abbrev head_op_0 := Operator.zoomStateT _ head_op (Lens₃ : Lens Env _)

def op :=
       reverse_op_0
  >>>> tail_op_0
  >>>> reverse_op_1
  >>>> head_op_0


namespace Benchmark

abbrev A := List Nat
abbrev B := Option Nat
abbrev ΔA := ΔList Nat ΔNat
abbrev ΔB := ΔOption Nat ΔNat


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

end Example7
