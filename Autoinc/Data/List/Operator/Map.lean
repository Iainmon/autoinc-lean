import Autoinc.Change
import Autoinc.Operator
import Autoinc.Data.List.Change

namespace ΔList
section Map

variable {M} [Monad M]
variable {A ΔA B ΔB : Type}

@[reducible] def map_op (op : Operator A B ΔA ΔB M) :
    Operator (List A) (List B)
             (ΔList A ΔA) (ΔList B ΔB)
             M where
  f xs := List.mapM op.f xs
  Δf Δl :=
    match Δl with
    | .ins i xs => ΔList.ins i <$> List.mapM op.f xs
    | .del i n => pure <| ΔList.del i n
    | .upd i Δxs => ΔList.upd i <$> List.mapM op.Δf Δxs

end Map
end ΔMap
