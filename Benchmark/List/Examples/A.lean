import Autoinc.Combinator
import Autoinc.Data.List.Operator
import Benchmark.Experiment
import Benchmark.List.Random

namespace Example1
/- tail -> tail -> tail -> head  -/
/-
digraph G {
  node [shape=box, fixedsize=true, width=1, height=1];
  input_0 [shape=none];

  input_0 -> tail_0;
  tail_0 -> tail_1;
  tail_1 -> tail_2;
  tail_2 -> head_0;
}
-/
open StructProd4
abbrev Env :=
  T (Thunk (List Nat))
    (Thunk (List Nat))
    (Thunk (List Nat))
    (Thunk (List Nat))

abbrev tail_op := ΔList.Tail.op (α:=Nat) (Δα:=ΔNat)
abbrev head_op := ΔList.Head.op (α:=Nat) (Δα:=ΔNat)

def tail_0 := Operator.zoomStateT IO (tail_op (LazyStateT (List Nat) IO)) (Lens₀ : Lens Env _)
def tail_1 := Operator.zoomStateT IO (tail_op (LazyStateT (List Nat) IO)) (Lens₁ : Lens Env _)
def tail_2 := Operator.zoomStateT IO (tail_op (LazyStateT (List Nat) IO)) (Lens₂ : Lens Env _)
def head_0 := Operator.zoomStateT IO (head_op (LazyStateT (List Nat) IO)) (Lens₃ : Lens Env _)

def op : Operator (List Nat) (Option Nat) (ΔList Nat ΔNat) (ΔOption Nat ΔNat) (StateT Env IO) :=
  tail_0 >>>> tail_1 >>>> tail_2 >>>> head_0


namespace Benchmark

abbrev A := List Nat
abbrev B := Option Nat
abbrev ΔA := ΔList Nat ΔNat
abbrev ΔB := ΔOption Nat ΔNat

instance : SizeOf A where
  sizeOf _ := 10000

/-
Type of changes: Insert / Delete / Update the input string
-/

abbrev input := List.range 10000
def case_1 : Case A B ΔA ΔB Env where
  op := op
  id := 1
  description := "insertion"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randIns 0 10000 size g |> Prod.fst

def case_2 : Case A B ΔA ΔB Env where
  op := op
  id := 2
  description := "deletion"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randDel 0 10000 size g |> Prod.fst

def case_3 : Case A B ΔA ΔB Env where
  op := op
  id := 3
  description := "update"
  rep := 100
  input := input
  p := 5
  genChange (g : StdGen) (size : Nat) :=
    randUpd 0 10000 size g |> Prod.fst

def cases :=
  [ case_1,
    case_2,
    case_3
  ]



end Benchmark



-- abbrev f := op.f
-- abbrev Δf := op.Δf

-- #eval StateT.run (f [1, 2, 3, 4]) default
-- #eval StateT.run (Δf (.ins 1 [2])) ([1, 2, 3, 4], [2, 3, 4], [3, 4], [4])



-- abbrev input := [1, 2, 3, 4, 5, 6]
-- #eval (testOp f Δf input (.ins 1 [2]) default).run
-- #eval (testOp f Δf input (.ins 0 [2, 3, 4]) default).run
-- #eval (testOp f Δf input (.ins 0 []) default).run
-- #eval (testOp f Δf input (.del 2 1) default).run
-- #eval (testOp f Δf input (.del 0 3) default).run
-- #eval (testOp f Δf input (.del 0 1) default).run
-- #eval (testOp f Δf input (.del 0 2) default).run




end Example1
