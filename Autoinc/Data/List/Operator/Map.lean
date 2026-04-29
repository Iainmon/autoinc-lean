import Autoinc.Change
import Autoinc.Operator
import Autoinc.Monad
import Autoinc.Data.List.Change
open Operator

namespace ΔMap

variable {m : Type → Type} [Monad m]
variable {α β Δα Δβ : Type}
variable [Change α Δα]
variable [Change β Δβ]
variable [Change (m β) (m Δβ)]
variable [Change (m (List β)) (m (ΔList β Δβ))]

section Map

@[simp,reducible]
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
#check Operator.valid

def map_op_spec
  (op : Operator α β Δα Δβ m)
  (spc : (map_op op).spec m) :
    (map_op op).spec m where
  valid := by
    simp only [map_op,Operator.valid]
    intros xs Δxs
    simp only [Operator.valid']
    intros h
    simp only [Change.valid]

    -- work here
    simp only [Operator.spec]



    simp_all only [map_op]
    simp_all only [Operator.valid]
    simp_all only [Operator.spec]

    simp_all only [map_op, Operator.valid]
    sorry
    -- op_valid m f spc.valid
  correct := sorry -- op_correct m f spc.correct


-- theorem op_valid'
--   (f : Operator α β Δα Δβ m)
--   (x : α) (dx : Δα)
--   (f_valid' : Operator.valid' m f x dx) :
--     Operator.valid' m f x dx := by
--   intro h


-- theorem op_valid
--   (f : Operator α β Δα Δβ m)
--   (f_valid : f.valid) : (op f).valid := by

--   intro xs Δxs h
--   match h with
--   | .ins i xs' =>
--     simp only [op, Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply f_valid
--     exact h_1 x hx
--   | .del i n =>
--     simp only [op, Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply f_valid
--     exact h_1 x hx
--   | .upd i Δxs' =>
--     simp only [op, Operator.f, List.mapM, ΔList.Δf]
--     apply List.mapM_valid
--     intro x hx
--     apply f_valid
--     exact h_1 x hx

-- #check Operator.valid'


-- #check (map_op m)

-- #check Operator.spec
-- #check (Operator.spec (m:=m))
-- #check (Operator.spec (m:=m) (op:=(map_op m op)))


-- #check 1

-- #check (Operator.spec (m:=m) (op:=(map_op m op)))

-- def spec : (map_op (α:=α) (Δα:=Δα) (m:=m)).spec m where
--   valid := op_valid m
--   correct := op_correct m


-- section MapGood
-- @[reducible]
-- def map_op (op : Operator α β Δα Δβ m) :
--     Operator (List α) (List β)
--              (ΔList α Δα) (ΔList β Δβ)
--              m where
--   f xs := List.mapM op.f xs
--   Δf Δl :=
--     match Δl with
--     | .ins i xs => ΔList.ins i <$> List.mapM op.f xs
--     | .del i n => pure <| ΔList.del i n
--     | .upd i Δxs => ΔList.upd i <$> List.mapM op.Δf Δxs


-- variable (op' : Operator α β Δα Δβ m)

-- #check op'


-- #check (op' : Operator α β Δα Δβ m)



-- #check map_op

-- #check Operator.valid'


-- #check (map_op m)

-- #check Operator.spec
-- #check (Operator.spec (m:=m))
-- #check (Operator.spec (m:=m) (op:=(map_op m op)))


-- #check 1

-- #check (Operator.spec (m:=m) (op:=(map_op m op)))

-- def spec : (map_op (α:=α) (Δα:=Δα) (m:=m)).spec m where
--   valid := op_valid m
--   correct := op_correct m


-- def spec' : (map_op (α:=α) (Δα:=Δα) (m:=m)).spec m where
--   valid := op_valid m
--   correct := op_correct m



-- -- theorem map_op_valid : (map_op op).valid := by
-- --   intro xs Δxs h
-- --   match h with
-- --   | .ins i xs' =>
-- --     simp only [map_op, Operator.f, List.mapM, ΔList.Δf]
-- --     apply List.mapM_valid
-- --     intro x hx
-- --     apply op.valid
-- --     exact h_1 x hx
-- --   | .del i n =>
-- --     simp only [map_op, Operator.f, List.mapM, ΔList.Δf]
-- --     apply List.mapM_valid
-- --     intro x hx
-- --     apply op.valid
-- --     exact h_1 x hx
-- --   | .upd i Δxs' =>
-- --     simp only [map_op, Operator.f, List.mapM, ΔList.Δf]
-- --     apply List.mapM_valid
-- --     intro x hx
-- --     apply op.valid
-- --     exact h_1 x hx


-- end MapGood


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
