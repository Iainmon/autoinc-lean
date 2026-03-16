import Autoinc.Operator
import Benchmark.Utils
import Benchmark.Table
import Benchmark.CSV

/-
  run experiements with
  - a given differential operator
  - a given input
  - a given change rate (change size / input size) : int
  - a change generator (for each type) : input -> input change
  - description of change type : int (the corresponding change description can be found in change cases)
  - repetition number
  output (string):
  change rate (%), change type (string),
  incremental computation time, non-incremental computation time, speedup
-/
namespace ExperimentReaderT

structure Output where
  ic : Float -- Elapsed time for incremental computation
  ph : Float -- Elapsed time for patching output change to output
  rc : Float -- Elapsed time for recomputation
deriving Repr


def Output.speedup (o : Output) : Float :=
  o.rc / o.ic

section
variable {α β Δα Δβ : Type} [Change α Δα] [Change β Δβ] [BEq β] [ToString α] [ToString β]
variable {m} [Monad m]
variable (input : α) (delta : Δα) [ToString Δα] [ToString Δβ]
variable {σ} [ToString σ]
variable (op : Operator α β Δα Δβ (StateT σ (ReaderT ρ IO)))

def execIO : StateT σ (ReaderT ρ IO) Output := do
  let input' := input ⨁ delta
  -- dbg_trace "[delta input] {delta}"
  -- set (σ:=σ) default

  -- let t₀ ← IO.monoNanosNow
  -- Initial computation
  let initRes ← op.f input
  let t₁ ← IO.monoNanosNow

  -- Differential computation
  let outputDelta ← op.Δf delta
  let t₂ ← IO.monoNanosNow

  -- Recomputation
  let recompRes ← op.f input'
  let t₃ ← IO.monoNanosNow

  let incRes ← pure (initRes ⨁ outputDelta)
  let t₄ ← IO.monoNanosNow
  -- dbg_trace "[delta output] {outputDelta}"

  let incTime := t₂ - t₁
  let recompTime := t₃ - t₂
  let patchTime := t₄ - t₃
  -- dbg_trace ("state 0: {s₀}, state 1: {s₁}, state 2: {s₂}").take 0
  if incRes == recompRes
  then return ⟨incTime |> Nat.toFloat,
               patchTime |> Nat.toFloat,
               recompTime |> Nat.toFloat⟩
  else
    IO.throwServerError s!"[Experiment.exec] Incremental result does not match recomputation result: \n Incremental: {incRes}\n Recomputed: {recompRes}"




def execNTimesIO (n : Nat) : StateT σ (ReaderT ρ IO) Output := do
  let res ← List.range n |> List.mapM
    (fun _ => execIO input delta op)
  let ic_times := filterIqr15 (List.map (·.ic) res)
  let ph_times := filterIqr15 (List.map (·.ph) res)
  let rc_times := filterIqr15 (List.map (·.rc) res)

  let ic_ts := mean ic_times
  let ph_ts := mean ph_times
  let rc_ts := mean rc_times

  pure ⟨ic_ts, ph_ts, rc_ts⟩

end

section
structure Case (α β Δα Δβ σ ρ : Type) where
  op : Operator α β Δα Δβ (StateT σ (ReaderT ρ IO))
  id : Nat -- the identifier of the
  description : String := "" -- the descrption of this test case
  rep : Nat -- repetition times
  input : α -- input
  p : Float -- percentage of the size of input change, e.g. 5 means 5%
  genChange : StdGen → Nat → Δα -- random change generator parameterized with the size

variable {α β Δα Δβ ε : Type} [Change α Δα] [Change β Δβ] [BEq β] [ToString α] [ToString β] [ToString Δα] [ToString Δβ] [SizeOf α]

variable {σ} {ρ} [Inhabited σ]
variable (p : ρ)
variable (case : Case α β Δα Δβ σ ρ)

def Case.exec : StateT σ (ReaderT ρ IO) Output := do
  let size := (case.p / 100.0) * (sizeOf case.input).toFloat |> (·.toUInt64.toNat)
  let gen ← IO.stdGenRef.get
  let dx := case.genChange gen size
  -- dbg_trace s!"Executing Case ID {case.id}: {case.description} with change size {size} using {dx}"
  execNTimesIO case.input dx case.op case.rep


def Case.dumpRes (o : Output) : List String :=
  let ⟨ic_ts, ph_ts, rc_ts⟩ := o
  [ toString case.id,
    toString $ case.p.trunc 3 ++ "%",
    toString $ ic_ts.trunc 3,
    toString $ ph_ts.trunc 3,
    toString $ rc_ts.trunc 3,
    toString $ o.speedup.trunc 3,
    case.description
  ]


def Case.headers := ["ID", "ΔSize", "IC (ns)", "PH (ns)", "RC (ns)", "Speedup", "Description"]


def Case.exec' : StateT σ (ReaderT ρ IO) Unit := do
  printTable
    headers
    (List.singleton $ dumpRes case (← case.exec))

def Case.execCSV : StateT σ (ReaderT ρ IO) Unit := do
  IO.println (toCSVString headers (List.singleton $ dumpRes case (← case.exec)))

def Case.execAllCSV' (cases : List (Case α β Δα Δβ σ ρ)) (caption : Option String := none) (i : String) : IO Unit := do
  let action : StateT σ (ReaderT ρ IO) Unit := do
    let rows ← cases.mapM (
      fun case => do pure $ dumpRes case (← case.exec)
    )
    let csv := toCSVString headers rows
    IO.FS.writeFile s!"data_{i}.csv" csv
  let a : ReaderT ρ IO PUnit := discard <| action default
  a.run p

def Case.execAll' (cases : List (Case α β Δα Δβ σ ρ)) (caption : Option String := none) : IO Unit := do
  let action : StateT σ (ReaderT ρ IO) Unit := do
    let rows ← cases.mapM (
      fun case => do pure $ dumpRes case (← case.exec)
    )
    printTable headers rows (caption:=caption)
  let a : ReaderT ρ IO PUnit := discard <| action default
  a.run p


def Case.execAllCSV (cases : List (Case α β Δα Δβ σ ρ)) (caption : Option String := none) : StateT σ (ReaderT ρ IO) Unit := do
  let rows ← cases.mapM (
    fun case => do pure $ dumpRes case (← case.exec)
  )
  let csv := toCSVString headers rows
  match caption with
  | some c => IO.println $ c ++ "\n\n"
  | none => pure ()

  IO.println csv
  IO.println "\n\n"
end
end ExperimentReaderT
