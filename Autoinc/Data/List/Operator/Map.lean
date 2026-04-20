import Autoinc.Change
import Autoinc.Operator
import Autoinc.Data.List.Change

section Map

-- variable {M} [Monad M]
-- variable {A ΔA B ΔB : Type}

-- @[reducible] def map_op (op : Operator A B ΔA ΔB M) :
--     Operator (List A) (List B)
--              (ΔList A ΔA) (ΔList B ΔB)
--              M where
--   f xs := List.mapM op.f xs
--   Δf Δl :=
--     match Δl with
--     | .ins i xs => ΔList.ins i <$> List.mapM op.f xs
--     | .del i n => pure <| ΔList.del i n
--     | .upd i Δxs => ΔList.upd i <$> List.mapM op.Δf Δxs

-- @[simp] lemma List.mapM_Id (f : A → Id B) (xs : List A) :
--   List.mapM f xs = List.map f xs := by
--   have h := @List.mapM_pure Id A B _ _ xs f
--   simp_all [pure]


-- variable [Change A ΔA] [Change B ΔB]

-- private instance : Setoid (Id B) := Eq_setoid
-- private instance : Setoid (Id (List B)) := Eq_setoid

-- theorem map_valid_Id (op : Operator A B ΔA ΔB Id) [S : op.spec] : (map_op op).valid := by
--   intro xs dx val_xs
--   simp
--   match dx with
--   | ΔList.ins i ys =>
--     simp_all only [Change.valid]
--     grind
--   | ΔList.del i k =>
--     simp_all only [Change.valid]
--   | ΔList.upd i ds =>
--     simp_all only [Change.valid]
--     by_cases h_ds : ds = [] <;> simp_all []
--     rw [← List.map_drop, ← List.map_take, List.forall₂_map_left_iff]
--     clear h_ds
--     induction ds generalizing i with
--     | nil => simp_all
--     | cons d ds ih =>
--       simp_all
--       rw [List.drop_eq_getElem_cons (by grind), List.take_succ_cons, List.forall₂_cons] at *
--       obtain ⟨x, ⟨val_x, val_ys⟩⟩ := val_xs
--       split_ands
--       · apply S.valid ; trivial
--       · apply ih; omega; simpa

-- theorem map_correct_Id (op : Operator A B ΔA ΔB Id) [S : op.spec] : (map_op op).correct := by
--   intro xs dx val_xs
--   simp
--   match dx with
--   | ΔList.ins i ys => simp_all []
--   | ΔList.del i k => simp_all
--   | ΔList.upd i ds =>
--     simp_all [HasEquiv.Equiv]
--     by_cases h_ds : ds = [] <;> simp_all []
--     simp [← List.map_drop, ← List.map_take, List.map_zipWith]
--     clear h_ds
--     obtain ⟨bound, val_ds⟩ := val_xs
--     induction ds generalizing i with
--     | nil => simp
--     | cons d ds ih =>
--       simp_all
--       rw [List.drop_eq_getElem_cons (by grind), List.take_succ_cons, List.forall₂_cons] at *
--       simp
--       split_ands
--       · have s := S.correct xs[i] d ; simp_all [Operator.correct', HasEquiv.Equiv]
--       · apply ih; omega; exact val_ds.2


-- syntax "map_simp_statemonad" : tactic
-- macro_rules
-- | `(tactic|map_simp_statemonad) =>
--   `(tactic|
--     (repeat (first
--     | simp only [defer_init, defer, before_after, Deferred.init, Deferred.defer, Deferred.before_after,
--         liftM, monadLift, MonadLift.monadLift, compute] at *
--     | simp only [bind, andThen, bind_pure_comp, map_pure, set,
--         StateT.pure, StateT.bind, StateT.modifyGet, StateT.get,
--         Functor.map, StateT.map, StateT.set, StateT.run, Id.run,
--         MonadStateOf.modifyGet, liftM, monadLift, MonadLift.monadLift, StateT.lift,
--         get, getThe, MonadStateOf.get, StateT.get] at *
--     | unfold StateT.bind at *
--     | unfold StateT.run at *
--     | unfold StateT.pure at *
--     | unfold update at *
--     | simp only [pure] at *
--     | simp only [update] at *
--     | simp only [modifyGet] at *
--     ))
--   )

-- attribute [simp] bind StateT.bind Functor.map StateT.map pure StateT.pure

-- @[simp, grind] lemma List.mapM_length_state {f : α → StateM σ β} {xs : List α} (h : xs.mapM' f st = (ys, st')) : ys.length = xs.length := by
--   induction xs generalizing ys st st' with
--   | nil => simp_all [StateT.pure]
--   | cons x xs ih =>
--     simp_all [bind, StateT.bind, StateT.pure]
--     cases h1 : f x st with
--     | mk ys1 st1 => cases h2 : mapM' f xs st1 with
--       | mk ys2 st2 => simp_all; grind

-- -- lemma List.getElem_mapM_state (xs : List α) (f : α → StateM σ β) (i : Nat) (ys : List β) {h_ix : i < xs.length} {h_iy : i < ys.length} :
-- --   List.mapM' f xs st = (ys,st') → ys[i] = (f xs[i]).1 := by
-- --   intro h
-- --   simp_all [List.getElem_map]

-- theorem map_valid_State (op : Operator A B ΔA ΔB (StateM σ)) [S : op.spec] : (map_op op).valid := by
--   intro xs dx val_xs st
--   simp
--   match dx with
--   | ΔList.ins i ys =>
--     simp_all only [Change.valid, List.isEmpty_iff]
--     simp [← List.mapM'_eq_mapM]
--     cases xs with
--     | nil => cases ys <;> cases val_xs <;> simp_all only [List.length_nil, nonpos_iff_eq_zero, List.mapM'_nil, pure,
--       StateT.pure, List.mapM'_cons, bind, StateT.bind, Id.eq_1, le_refl, or_true, true_or, reduceCtorEq]
--     | cons x xs =>
--       simp_all only [List.length_cons, List.mapM'_cons, bind, StateT.bind, pure, StateT.pure]
--       cases h1 : op.f x st with | mk a1 b1; simp_all only
--       cases h2 : List.mapM' op.f xs b1 with | mk a2 b2; simp_all only [Id.eq_1, List.length_cons]
--       cases h3 : List.mapM' op.f ys b2 with | mk a3; simp_all only
--       cases val_xs <;> try simp_all only [Id.eq_1, List.mapM'_nil, pure, StateT.pure, Prod.mk.injEq, List.nil_eq, true_or]
--       rw [@List.mapM_length_state _ _ _ b1 a2 b2 op.f xs] at * <;> simp_all only [or_true]
--   | ΔList.del i k =>
--     simp_all only [Change.valid]
--     simp only [pure, StateT.pure, ← List.mapM'_eq_mapM]
--     cases h : List.mapM' op.f xs st with | mk a1 b1; simp_all only
--     rw [@List.mapM_length_state _ _ _ st a1 b1 op.f xs] at * <;> simp_all only
--   | ΔList.upd i ds =>
--     simp_all only [Change.valid]
--     by_cases h_ds : ds = [] <;> simp_all only [List.isEmpty_nil, List.length_nil, add_zero,
--       List.take_zero, List.forall₂_nil_right_iff, and_true, true_or, bind, ← List.mapM'_eq_mapM,
--       Id.eq_1, StateT.map, List.mapM'_nil, pure, StateT.pure]
--     · split ; simp_all only
--     · cases h : List.mapM' op.f xs st with | mk ys st1; simp_all only [List.isEmpty_iff, false_or]
--       cases h2 : List.mapM' op.Δf ds st1 with | mk ds1 st2; simp_all only
--       rw [@List.mapM_length_state _ _ _ st ys st1 op.f xs] at * <;> try simp_all only
--       rw [@List.mapM_length_state _ _ _ st1 ds1 st2 op.Δf ds] at * <;> simp_all only [true_and]
--       right
--       clear h_ds
--       obtain ⟨bound, val_xs⟩ := val_xs

--       induction ds generalizing st st1 ds1 st2 ys i with
--       | nil => simp_all only [Id.eq_1, List.mapM'_nil, pure, StateT.pure, Prod.mk.injEq,
--         List.nil_eq, List.length_nil, add_zero, List.take_zero, List.forall₂_nil_right_iff]
--       | cons d ds ih =>
--         simp_all
--         cases h3 : op.Δf d st1 with | mk d1 st3 ; simp_all
--         cases h4 : List.mapM' op.Δf ds st3 with | mk ds1 st4 ; simp_all
--         rcases h2 with ⟨hp, hq⟩
--         -- have hst : st1 = st3 := sorry
--         subst hp hq
--         rw [List.drop_eq_getElem_cons (by grind), List.take_succ_cons, List.forall₂_cons] at *
--         obtain ⟨val_d, val_ds⟩ := val_xs
--         split_ands
--         · clear val_ds
--           have s := S.valid xs[i] d ; simp_all [Operator.valid]
--           sorry
--         · apply ih
--           simpa
--           sorry
--           grind
--           trivial
--           sorry


end Map
