import Lake
open System Lake DSL

package autoinc where

@[default_target]
lean_lib Autoinc where
  precompileModules := true

lean_lib Benchmark

lean_exe benchmark where
  root := `Benchmark.Main


require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

require "leanprover-community" / "mathlib"

require assertCmd from git
  "https://github.com/pnwamk/lean4-assert-command" @ "main"
