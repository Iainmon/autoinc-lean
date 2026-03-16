import Autoinc.Operator

namespace Flatten
/-
Flatten `List (List Δ)` to `List Δ` (`Δ` refers to a change type)
-/

variable {T ΔT : Type} [Change T ΔT]
variable {m : Type → Type} [Monad m]
def op : Operator T T (List (List ΔT)) (List ΔT) m where
  f := pure
  Δf := pure ∘ List.flatten

end Flatten
