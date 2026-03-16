-- import Autoinc.Change
-- import Autoinc.Partial
-- import Autoinc.Data.Nat.Change


-- namespace Div
-- /- An differential operator for division -/
-- variable (m : Type → Type) [MonadStateOf (Nat × Nat) m] [ChangeMonad m]
-- @[simp] def partial_op : PartialOperator Nat Nat Nat ΔNat ΔNat (List ΔNat) m where
--   f x y := modifyGet (fun _ => (x / y, (x, y)))
--   δf_1 dx := modifyGet (fun (x, y) => let x' := x ⨁ dx; ([(x'/y) ⊖ (x/y)], (x', y)))
--   δf_2 dy := modifyGet (fun (x, y) => let y' := y ⨁ dy; ([(x/y') ⊖ (x/y)], (x, y')))

-- def div_op := partial_op m |> PartialOperator.toOperator


-- variable [ChangeMonad m] [LawfulChangeMonad m] [LawfulMonadStateOf (Nat × Nat) m]
-- open LawfulChangeMonad LawfulMonadStateOf
-- theorem valid_1 : (partial_op m).valid_1 := by
--   simp
--   intro a b dx hv
--   match dx with
--   | .inc da =>
--     simp_all  [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
--     apply mprop_bind_const_pure ; sorry
--   | .dec c =>
--     simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
--     apply mprop_bind_const_pure ; sorry

-- theorem valid_2 : (partial_op m).valid_2 := by
--   simp
--   intro a b dx hv
--   match dx with
--   | .inc da =>
--     simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
--     apply mprop_bind_const_pure ; sorry
--   | .dec c =>
--     simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq]
--     apply mprop_bind_const_pure; sorry


-- theorem correct_1 : (partial_op m).correct_1 := by
--   intro a b dx hv
--   cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq] <;> congr <;> funext <;> congr <;> sorry


-- theorem correct_2 : (partial_op m).correct_2 := by
--   intro a b dx hv
--   cases dx <;> simp_all [←bind_pure_comp, seq_eq_bind_map, modifyGet_eq] <;> congr <;> funext <;> congr <;> sorry
-- def partial_spec : (partial_op m).spec where
--   valid_1 := valid_1 m
--   valid_2 := valid_2 m
--   correct_1 := correct_1 m
--   correct_2 := correct_2 m

-- def spec := PartialOperator.toOperatorSpec (partial_op m) (partial_spec m)

-- end Div
