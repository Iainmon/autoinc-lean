import Autoinc.Change
import Autoinc.Operator
import Autoinc.Monad
import Autoinc.Data.List.Change

namespace ΔMap
section Map


section MapGood
variable {m : Type → Type} [Monad m]
variable {α β Δα Δβ : Type}
variable [Change α Δα]
variable [Change (m β) (m Δβ)]
variable (op : Operator α β Δα Δβ m)

#check op


#check (op : Operator α β Δα Δβ m)

@[reducible]
def map_op (op : Operator α β Δα Δβ m) :
    Operator (List α) (List β)
             (ΔList α Δα) (ΔList β Δβ)
             m where
  f xs := List.mapM op.f xs
  Δf Δl :=
    match Δl with
    | .ins i xs => ΔList.ins i <$> List.mapM op.f xs
    | .del i n => pure <| ΔList.del i n
    | .upd i Δxs => ΔList.upd i <$> List.mapM op.Δf Δxs


#check map_op


end MapGood

-- theorem map_op'_valid {α β Δα Δβ m} (op : Operator α β Δα Δβ m) : (map_op' op).valid := by sorry

-- variable (m : Type → Type) [Monad m]
-- variable {α β Δα Δβ : Type} [Change α Δα] [Change β Δβ]

-- theorem map_op'_valid {α β Δα Δβ m} (op : Operator α β Δα Δβ m) :
--   (map_op' op).valid := by
--   intro xs Δxs h
--   match h with
--   | .ins i xs' =>
--     simp only [map_op', Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply op.valid
--     exact h_1 x hx
--   | .del i n =>
--     simp only [map_op', Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply op.valid
--     exact h_1 x hx
--   | .upd i Δxs' =>
--     simp only [map_op', Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply op.valid
--     exact h_1 x hx


namespace Old
-- variable {α Δα : Type} [Change α Δα]
-- variable {β Δβ : Type} [Change β Δβ]
-- variable (m : Type → Type) [LazyMonadStateOf (List α) m]
-- variable [MonadStateOf β m] [MonadReaderOf (α → β) m]

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
end Old

end Map
end ΔMap
