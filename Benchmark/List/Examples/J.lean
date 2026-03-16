import Autoinc.Combinator
import Autoinc.Data.Seq.Operator
import Autoinc.Data.Nat.Operator
import Benchmark.List.Operators
import Benchmark.Utils
import Benchmark.Experiment
import Benchmark.List.Random
import AssertCmd


namespace Example10
/- cons -> cons -> append -> reverse -> head -/
/-
    digraph G {
      node [shape=box, fixedsize=true, width=1, height=1];
      input_0_nat [shape=none];
      input_1_list [shape=none];
      input_2_nat [shape=none];
      input_3_list [shape=none];

      input_0_nat -> cons_0;
      input_1_list -> cons_0;
      input_2_nat -> cons_1;
      input_3_list -> cons_1;
      cons_0 -> append;
      cons_1 -> append;
      append -> reverse;
    }
-/
open StructProd3
abbrev cons_op := ΔList.Cons.op (α:=Nat) (Δα:=ΔNat)
abbrev append_op := ΔList.Append.partial_op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)
abbrev reverse_op := ΔList.Reverse.op (α:=Nat) (Δα:=ΔNat) (StateT Nat IO)
abbrev head_op := ΔList.Head.op (α:=Nat) (Δα:=ΔNat) (LazyStateT (List Nat) IO)

abbrev Append_0_ST := Nat
abbrev Reverse_0_ST := Nat
abbrev Head_0_ST := Thunk (List Nat)


abbrev Env := T
  Append_0_ST      /- append -/
  Reverse_0_ST     /- reverse -/
  Head_0_ST        /- head -/






def append_0 :=
  PartialOperator.zoomStateT IO append_op (Lens₀ : Lens Env Nat) |>
  PartialOperator.toSeq₁ |>
  PartialOperator.toSeq₂ |>
  PartialOperator.toOperator

def reverse_0 :=
  Operator.zoomStateT IO reverse_op (Lens₁ : Lens Env _) |>
  Operator.toSeq

def head_0 :=
  Operator.zoomStateT IO head_op (Lens₂ : Lens Env _) |>
  Operator.toSeq



def op := (cons_op _ **** cons_op _) >>>> append_0 >>>> Flatten.op >>>> Flatten.op >>>> reverse_0 >>>> head_0





namespace Benchmark

abbrev A := (Nat × List Nat) × (Nat × List Nat)
abbrev B := Option Nat
abbrev ΔA := ΔProd (ΔProd ΔNat (ΔList Nat ΔNat)) (ΔProd ΔNat (ΔList Nat ΔNat))
abbrev ΔB := List (ΔOption Nat ΔNat)

instance : SizeOf A where
  sizeOf _ := 10000

abbrev input₁ := 1
abbrev input₂ := List.range 10000
abbrev input₃ := 1
abbrev input₄ := List.range' 10000 20000
abbrev input := ((input₁, input₂), (input₃, input₄))

def buildCase (id : Nat) (decription : String) (genChange : StdGen → Nat → ΔA) (rep:Nat:=500) : Case A B ΔA ΔB Env where
  op := op
  id := id
  description := decription
  rep := rep
  input := input
  p := 5
  genChange := genChange

def case_1 :=
  buildCase
    1
    "insertion in the first operand of cons_0"
    (fun g size => randIns 0 10000 size g |> Prod.fst |> ΔProd.first_2)

def case_2 :=
  buildCase
    2
    "deletion in the first operand of cons_0"
    (fun g size => randDel 0 10000 size g |> Prod.fst |> ΔProd.first_2)

def case_3 :=
  buildCase
    3
    "updating in the first operand of cons_0"
    (fun g size => randUpd 0 10000 size g |> Prod.fst |> ΔProd.first_2)

def case_4 :=
  buildCase
    4
    "insertion in the second operand of cons_1"
    (fun g size => randIns 0 10000 size g |> Prod.fst |> fun x => ΔProd._2 (ΔProd._2 x))


def case_5 :=
  buildCase
    5
    "deletion in the second operand of cons_1"
    (fun g size => randDel 0 10000 size g |> Prod.fst |> fun x => ΔProd._2 (ΔProd._2 x))

def case_6 :=
  buildCase
    6
    "updating in the second operand of cons_1"
    (fun g size => randUpd 0 10000 size g |> Prod.fst |> fun x => ΔProd._2 (ΔProd._2 x))




def cases := [case_1, case_2, case_3, case_4, case_5, case_6]





end Benchmark



end Example10
