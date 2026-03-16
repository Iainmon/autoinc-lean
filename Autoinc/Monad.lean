import Autoinc.Change
import Batteries.Control.LawfulMonadState
import Lean

-- Simplify expressions involving ID, reader, and state monads
syntax "monad_simp" : tactic
macro_rules
| `(tactic|monad_simp) =>
  `(tactic|simp_all
    [HasEquiv.Equiv,
    bind, bind_pure_comp, map_pure, set, pure,
    StateT.pure, StateT.bind, StateT.modifyGet, StateT.get,
    Functor.map, StateT.map, StateT.set, Id.run,
    ReaderT.pure, ReaderT.run, ReaderT.bind, StateT.run
    ])


class ChangeMonad m extends Monad m where
  mprop : m Prop → Prop

attribute [simp] ChangeMonad.mprop


namespace ChangeMonad

variable {m : Type → Type} [ChangeMonad m]

instance ChangeMonad.Change [Change α Δα] : Change (m α) (m Δα) where
  patch f Δf := (· ⨁ ·) <$> f <*> Δf
  valid f Δf := mprop $ (· ⊢ ·) <$> f <*> Δf

/- `ChangeMonad` for `Id`  -/
scoped instance IdChange : ChangeMonad Id where
  mprop mp := mp.run

/- `ChangeMonad` for `ReaderT` -/
scoped instance ReaderTChange [ChangeMonad m] : ChangeMonad (ReaderT ρ m) where
  mprop mp := ∀ p, mprop <| mp.run p

/- `ChangeMonad` for `StateT` -/
scoped instance StateTChange [ChangeMonad m] : ChangeMonad (StateT σ m) where
  mprop mp := ∀ s, mprop <| Prod.fst <$> mp.run s

attribute [simp] ChangeMonad.Change

end ChangeMonad


open ChangeMonad in
@[grind] class LawfulChangeMonad m [ChangeMonad m] extends LawfulMonad m where
  mprop_pure {p : Prop} (h : p) : mprop (pure p : m Prop)
  mprop_bind_const_pure {α} {f : m α} {p : Prop} (h : p) : mprop (f >>= (fun _ => pure p))
  mprop_weaken {α β γ} {ma : m α} {mb : α → m β} {mc : β → m γ} {p : α  → β → Prop} :
    mprop (do let x ← ma; p x <$> mb x) →
    mprop (do let x ← ma; let y ← mb x; (fun _ => p x y) <$> mc y)
  mprop_conj {α β γ} {ma : m α} {mb : α → m β} {mc : β → m γ} {p q : α → β → γ → Prop} :
    mprop (do let x ← ma; let y ← mb x; p x y <$> mc y) →
    mprop (do let x ← ma; let y ← mb x; q x y <$> mc y) →
    mprop (do let x ← ma; let y ← mb x; (fun z => p x y z ∧ q x y z) <$> mc y)



namespace LawfulChangeMonad
open ChangeMonad
variable {α Δα : Type} [Change α Δα]
variable {m : Type → Type} [ChangeMonad m] [LawfulChangeMonad m]

@[simp, grind .] theorem valid_pure {a : α} {Δa : Δα} (val_a : a ⊢ Δa) :
  (pure a : m α) ⊢ (pure Δa : m Δα) := by
    simp [Change.valid]; exact mprop_pure val_a

@[simp] theorem patch_pure {a : α} {Δa : Δα} :
  ChangeMonad.Change.patch (pure a : m α) (pure Δa : m Δα) = (pure (a ⨁ Δa) : m α) := by simp [Change.patch]

@[simp] theorem mprop_map_const {f : m α} {p : Prop} (h : p) :
  mprop ((fun _ => p) <$> f) := by
    simp only [← bind_pure_comp]
    exact (mprop_bind_const_pure h)

@[simp] theorem pure_1 {p : Prop} (mx : m α) (h : p) :
  ChangeMonad.mprop (do mx >>= (fun _ => pure p) : m Prop) :=
  by exact (mprop_bind_const_pure h)

@[simp] theorem pure_2 {p : Prop} (mx : m α) (my : α → m β) (h : p) :
  ChangeMonad.mprop (do mx >>= fun x => my x >>= (fun _ => pure p) : m Prop) :=
  by intros; simp only [←bind_assoc]; exact (mprop_bind_const_pure h)

@[simp] theorem pure_3 {p : Prop} (mx : m α) (my : α → m β) (mz : β → m γ) (h : p) :
  ChangeMonad.mprop (do mx >>= fun x => my x >>= fun y => mz y >>= (fun _ => pure p) : m Prop) :=
  by intros; simp only [←bind_assoc]; exact (mprop_bind_const_pure h)



attribute [local simp] bind pure Id.run bind_pure_comp

instance LawfulIdChangeMonad : LawfulChangeMonad Id where
  mprop_pure h := h
  mprop_bind_const_pure h := h
  mprop_weaken h := by monad_simp
  mprop_conj h₁ h₂ := by monad_simp

instance LawfulReaderTChangeMonad : LawfulChangeMonad (ReaderT ρ m) where
  mprop_pure h r := by monad_simp ; grind only [mprop_pure]
  mprop_bind_const_pure h r := by monad_simp
  mprop_weaken h s := by
    monad_simp; exact mprop_weaken (h s)
  mprop_conj h₁ h₂ s := by
    monad_simp; exact mprop_conj (h₁ s) (h₂ s)

instance LawfulStateTChangeMonad : LawfulChangeMonad (StateT σ m) where
  mprop_pure h s := by monad_simp ; grind only [mprop_pure]
  mprop_bind_const_pure h s := by monad_simp
  mprop_weaken h s := by
    monad_simp; exact mprop_weaken (h s)
  mprop_conj h₁ h₂ s := by
    monad_simp; exact mprop_conj (h₁ s) (h₂ s)


end LawfulChangeMonad



namespace LawfulMonadStateOf

@[simp] theorem modifyGet_modifyGet [Monad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m]
  (f : σ → α × σ) (g : σ → β × σ) (h : α → β → γ) :
  (do
    let x ← (modifyGet f : m α)
    let Δx ← (modifyGet g : m β)
    pure (h x Δx))
  =
  (modifyGet (fun s₀ =>
    let (a, s₁) := f s₀
    let (b, s₂) := g s₁
    (h a b, s₂)))
    := by simp [LawfulMonadStateOf.modifyGet_eq]
end LawfulMonadStateOf

-- Simplify expressions involving change monads
syntax "cmsimp" : tactic
macro_rules
| `(tactic | cmsimp) =>
  `(tactic | simp_all [LawfulMonadStateOf.modifyGet_eq, ← bind_pure_comp,
    LawfulMonadStateOf.get_bind_const, pure_bind, bind_assoc,
    seq_eq_bind_map, LawfulMonadStateOf.set_bind_get_bind, LawfulMonadStateOf.set_bind_set_bind, modify])

-- When the goal is in form `ChangeMonad (set ...; p)`, use this tactic
syntax "set_elim" : tactic
macro_rules
| `(tactic | set_elim) =>
  `(tactic | apply LawfulChangeMonad.mprop_bind_const_pure)

open Lean Meta Elab Tactic


elab "monad_eq" : tactic => do
  let target ← whnf (← getMainTarget)

  -- 1. Ensure the goal is an Equality
  if let some (_, lhs, rhs) := target.eq? then

    -- 2. Switch on the structure of the Left-Hand Side
    match_expr lhs with

    ------------------------------------------------------
    -- CASE A: Monadic Bind (lhs = _ >>= _)
    -- Signature: Bind.bind {m} {inst} {α} {β} ma fa (6 args)
    ------------------------------------------------------
    | Bind.bind _ _ _ _ _ _ =>
        match_expr rhs with
        | Bind.bind _ _ _ _ _ _ =>
            -- logInfo "Match: Bind = Bind. Applying congruence."
            evalTactic (← `(tactic| congr 1))
        | _ => throwError "LHS is Bind, but RHS is not."

    ------------------------------------------------------
    -- CASE B: MonadState Set (lhs = set _)
    -- Signature: MonadStateOf.set {σ} {m} {inst} s (4 args)
    ------------------------------------------------------
    | MonadStateOf.set _ _ _ _ =>
        match_expr rhs with
        | MonadStateOf.set _ _ _ _ =>
            -- logInfo "Match: MonadStateOf.set _ = MonadStateOf.set _; Applying congr 1."
            -- We assume the monad is defined as a function (like StateT)
            evalTactic (← `(tactic| congr 1))
        | _ => throwError "LHS is Set, but RHS is not."
    | Pure.pure _ _ _ _ =>
        match_expr rhs with
        | Pure.pure _ _ _ _ =>
            -- logInfo "Match: pure _ = pure _; Applying congr 1."
            evalTactic (← `(tactic| congr 1))
        | _ => throwError "LHS is pure, but RHS is not."
    -- Case C: Lambda Functions & Fallback
    -- Lambdas have no head constant, so they fall through to here.
    | _ =>
       let lhsType ← inferType lhs
       -- Check if the type is a function (forall)
       if (← whnf lhsType).isForall then
        --  logInfo "Match: fun _ => _ = fun _ => _; Applying funext."
         evalTactic (← `(tactic| apply funext; intro))
       else
         throwError "No matching pattern found"

  else
    throwError m!"Goal is not an equality. The goal type is: {target}"

macro "solve_monad_eq" : tactic => `(tactic| repeat (any_goals monad_eq))

class LawfulMonadReaderOf (ρ : Type) (m : Type → Type) [Monad m] [MonadReaderOf ρ m] extends LawfulMonad m where
  read_bind_read {α} (mx : ρ → ρ → m α) : (do let p₁ ← read; let p₂ ← read; mx p₁ p₂) = (do let p₁ ← read; mx p₁ p₁)
  read_swap (mx₁ : m γ) (mx₂ : γ → ρ → m α) : (do let y ← mx₁; let p ← read; mx₂ y p) = (do let p ← read; let y ← mx₁; mx₂ y p)

instance {m ρ} [Monad m] [LawfulMonad m] : LawfulMonadReaderOf ρ (ReaderT ρ m) where
  read_bind_read {α} mx := by
    simp_all [read, readThe, MonadReaderOf.read, ReaderT.read, bind]
    unfold ReaderT.bind
    simp_all
  read_swap {α} mx₁ mx₂ := by
    simp_all [read, readThe, MonadReaderOf.read, ReaderT.read, bind]
    unfold ReaderT.bind
    simp_all
