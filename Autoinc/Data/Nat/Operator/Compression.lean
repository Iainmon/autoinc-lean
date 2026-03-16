import Autoinc.Data.Nat.Change
import Autoinc.Operator


namespace ΔNat
namespace Compression

variable {m : Type → Type} [Monad m]

def op : Operator Nat Nat (List ΔNat) ΔNat m where
  f := pure
  Δf := List.foldl g (pure $ ΔNat.inc 0) where
    g d₁ d₂ := do pure $ NatChange.concat (← d₁) d₂

end Compression
end ΔNat
