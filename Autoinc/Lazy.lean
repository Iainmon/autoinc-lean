import Batteries.Control.LawfulMonadState

class LazyMonadStateOf (σ : Type) (m : Type → Type)
    extends MonadStateOf σ m where
  lazyModify : (σ → σ) → m PUnit

export LazyMonadStateOf (lazyModify)

abbrev lazyModifyThe (σ : Type) {m} [LazyMonadStateOf σ m] (f : σ → σ) : m PUnit :=
  LazyMonadStateOf.lazyModify f

abbrev LazyStateT (σ : Type) (m : Type → Type) (α : Type) :=
  StateT (Thunk σ) m α

instance {m σ} [Monad m] : MonadStateOf σ (LazyStateT σ m) where
  get := do let t ← StateT.get; return t.get
  set s := StateT.set (Thunk.pure s)
  modifyGet f := do
    let t ← StateT.get
    let (a, s) := f t.get
    StateT.set (Thunk.pure s)
    return a

instance {m σ} [Monad m] : LazyMonadStateOf σ (LazyStateT σ m) where
  lazyModify f := do
    let t ← StateT.get
    let newT := t.map f
    StateT.set newT

instance {m σ} [Monad m] : LazyMonadStateOf σ (StateT σ m) where
  lazyModify := modify


abbrev LazyStateT₂ (σ₁ σ₂ : Type) (m : Type → Type) (α : Type) :=
  StateT (Thunk σ₁ × Thunk σ₂) m α

instance {m σ₁ σ₂} [Monad m] : MonadStateOf σ₁ (LazyStateT₂ σ₁ σ₂ m) where
  get := do let t ← StateT.get; return t.1.get
  set s := StateT.modifyGet (fun (_, t₂) => (PUnit.unit, (s, t₂)))
  modifyGet f := do
    let (t₁, t₂) ← StateT.get
    let (a, s₁) := f t₁.get
    StateT.set (Thunk.pure s₁, t₂)
    return a

instance {m σ₁ σ₂} [Monad m] : LazyMonadStateOf σ₁ (LazyStateT₂ σ₁ σ₂ m) where
  lazyModify f := do
    let (t₁, t₂) ← StateT.get
    let newT := t₁.map f
    StateT.set (newT, t₂)

instance {m σ₁ σ₂} [Monad m] : MonadStateOf σ₂ (LazyStateT₂ σ₁ σ₂ m) where
  get := do let t ← StateT.get; return t.2.get
  set s := StateT.modifyGet (fun (t₁, _) => (PUnit.unit, (t₁, s)))
  modifyGet f := do
    let (t₁, t₂) ← StateT.get
    let (a, s₂) := f t₂.get
    StateT.set (t₁, Thunk.pure s₂)
    return a

instance {m σ₁ σ₂} [Monad m] : LazyMonadStateOf σ₂ (LazyStateT₂ σ₁ σ₂ m) where
  lazyModify f := do
    let (t₁, t₂) ← StateT.get
    let newT := t₂.map f
    StateT.set (t₁, newT)



structure LazyEagerState σ θ where
  s₁ : Thunk σ
  s₂ : θ

instance [Inhabited σ] [Inhabited θ] : Inhabited (LazyEagerState σ θ) where
  default := {
    s₁ := Thunk.pure default
    s₂ := default
  }

instance [ToString σ] [ToString θ]  : ToString (LazyEagerState σ θ) where
  toString | ⟨s₁, s₂⟩ => s!"() => {toString s₁.get}, {toString s₂}"


abbrev LazyEagerStateT (σ θ : Type) (m : Type → Type) (α : Type) :=
  StateT (LazyEagerState σ θ) m α

instance {m σ θ} [Monad m] : MonadStateOf σ (LazyEagerStateT σ θ m) where
  get := do let t ← StateT.get; return t.s₁.get
  set s :=
    StateT.modifyGet (fun st => (PUnit.unit, {st with s₁ := Thunk.pure s}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s₁) := f st.s₁.get
    StateT.set {st with s₁ := Thunk.pure s₁}
    return a

instance {m σ θ} [Monad m] : LazyMonadStateOf σ (LazyEagerStateT σ θ m) where
  lazyModify f := do
    let st ← StateT.get
    let newT := st.s₁.map f
    StateT.set {st with s₁ := newT}

instance {m σ θ} [Monad m] : MonadStateOf θ (LazyEagerStateT σ θ m) where
  get := do let t ← StateT.get; return t.s₂
  set s :=
    StateT.modifyGet (fun st => (PUnit.unit, {st with s₂ := s}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s₂) := f st.s₂
    StateT.set {st with s₂ := s₂}
    return a



structure LazyEagerState2 σ₁ σ₂ θ₁ θ₂ where
  s1 : Thunk σ₁
  s2 : Thunk σ₂
  s3 : θ₁
  s4 : θ₂

instance [Inhabited σ₁] [Inhabited σ₂] [Inhabited θ₁] [Inhabited θ₂] : Inhabited (LazyEagerState2 σ₁ σ₂ θ₁ θ₂) where
  default := {
    s1 := Thunk.pure default
    s2 := Thunk.pure default
    s3 := default
    s4 := default
  }

instance [ToString σ₁] [ToString σ₂] [ToString θ₁] [ToString θ₂] : ToString (LazyEagerState2 σ₁ σ₂ θ₁ θ₂) where
  toString | ⟨s₁, s₂, s₃, s₄⟩ => s!"{toString s₁.get}, {toString s₂.get}, {toString s₃}, {toString s₄}"

abbrev LazyEagerStateT₂ (σ₁ σ₂ : Type) (θ₁ θ₂ : Type) (m : Type → Type) (α : Type) :=
  StateT (LazyEagerState2 σ₁ σ₂ θ₁ θ₂) m α

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : MonadStateOf σ₁ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  get := do let t ← StateT.get; return t.s1.get
  set s := StateT.modifyGet (fun st => (PUnit.unit, {st with s1 := Thunk.pure s}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s₁) := f st.s1.get
    StateT.set {st with s1 := Thunk.pure s₁}
    return a

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : LazyMonadStateOf σ₁ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  lazyModify f := do
    let st ← StateT.get
    let newT := st.s1.map f
    StateT.set {st with s1 := newT}

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : MonadStateOf σ₂ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  get := do let t ← StateT.get; return t.s2.get
  set s := StateT.modifyGet (fun st => (PUnit.unit, {st with s2 := Thunk.pure s}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s₂) := f st.s2.get
    StateT.set {st with s2 := Thunk.pure s₂}
    return a

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : LazyMonadStateOf σ₂ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  lazyModify f := do
    let st ← StateT.get
    let newT := st.s2.map f
    StateT.set {st with s2 := newT}

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : MonadStateOf θ₁ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  get := do let t ← StateT.get; return t.s3
  set s1 := StateT.modifyGet (fun st => (PUnit.unit, {st with s3 := s1}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s3) := f st.s3
    StateT.set {st with s3 := s3}
    return a

instance {m σ₁ σ₂ θ₁ θ₂} [Monad m] : MonadStateOf θ₂ (LazyEagerStateT₂ σ₁ σ₂ θ₁ θ₂ m) where
  get := do let t ← StateT.get; return t.s4
  set s2 := StateT.modifyGet (fun st => (PUnit.unit, {st with s4 := s2}))
  modifyGet f := do
    let st ← StateT.get
    let (a, s4) := f st.s4
    StateT.set {st with s4 := s4}
    return a

class LawfulLazyMonadStateOf (σ : Type) (m : Type → Type)
    [Monad m] [LazyMonadStateOf σ m]
    extends LawfulMonadStateOf σ m where
  lazyModify_eq (f : σ → σ) : lazyModify (m:=m) f = modify (m:=m) f

instance [Monad m] [LawfulMonad m] : LawfulMonad (LazyStateT σ m) where
  id_map := id_map
  map_const := map_const
  pure_bind := pure_bind
  bind_pure_comp := bind_pure_comp
  seqLeft_eq := seqLeft_eq
  seqRight_eq := seqRight_eq
  pure_seq := pure_seq
  bind_assoc := bind_assoc
  bind_map := bind_map

instance [Monad m] [LawfulMonad m] : LawfulMonadStateOf σ (LazyStateT σ m) where
  modifyGet_eq f := by
    apply StateT.ext
    intro s
    simp only [get, getThe, MonadStateOf.get, StateT.run, pure, StateT.pure, StateT.bind, bind, modifyGet, MonadStateOf.modifyGet, StateT.bind, StateT.set, StateT.get, map_eq_pure_bind, ]
    simp [Thunk.get, set, StateT.set]
  get_bind_const mx := by
    apply StateT.ext
    intro s
    simp only [get, getThe, MonadStateOf.get]
    simp [StateT.run, StateT.get, pure, StateT.pure, StateT.bind, bind]
  get_bind_get_bind mx := by
    apply StateT.ext
    intro s
    simp only [get, getThe, MonadStateOf.get]
    simp [StateT.run, StateT.get, pure, StateT.pure, StateT.bind, bind]
  get_bind_set_bind mx := by
    apply StateT.ext
    intro s
    simp only [get, getThe, MonadStateOf.get]
    simp [StateT.run, StateT.get, pure, StateT.pure, StateT.bind, bind, Thunk.get, set, StateT.set, Thunk.pure]
  set_bind_get s := by
    apply StateT.ext
    intro s
    simp only [get, getThe, MonadStateOf.get]
    simp [StateT.run, StateT.get, pure, StateT.pure, StateT.bind, bind, Thunk.get, set, StateT.set, Thunk.pure]
  set_bind_set s := by
    intro s
    simp only [set, Thunk.pure]
    apply StateT.ext
    simp [StateT.run, StateT.bind, bind, StateT.set]

open LawfulMonadStateOf in
instance [Monad m] [LazyMonadStateOf σ m] [LawfulMonad m]
: LawfulLazyMonadStateOf σ (LazyStateT σ m) where
  lazyModify_eq f := by
    simp only [lazyModify, modify, modifyGet_eq, set, Thunk.map, Thunk.get, get, getThe, MonadStateOf.get, bind_pure_comp, Functor.map_map, id_map',
      bind_map_left]; rfl

attribute [simp] LawfulLazyMonadStateOf.lazyModify_eq


syntax "lazy_simp" : tactic
local macro_rules
| `(tactic | lazy_simp) =>
  `(tactic | simp_all (config := {singlePass := true}) only [get, getThe, MonadStateOf.get, StateT.run, pure, StateT.pure, StateT.bind, bind, modifyGet, MonadStateOf.modifyGet, StateT.get, map_eq_pure_bind, liftM, set, StateT.set, monadLift, MonadLift.monadLift, StateT.lift, Thunk.pure, Thunk.get, Thunk.map, lazyModify, modify, LawfulMonadStateOf.modifyGet_eq, SeqRight.seqRight] <;> try simp
   )

syntax "mysimp" : tactic
local macro_rules
| `(tactic | mysimp) =>
  `(tactic |
    {
    apply StateT.ext
    intro s₁
    apply StateT.ext
    intro s₂
    lazy_simp
    }
  )

section
variable (σ₁ σ₂ : Type) (m : Type → Type) [Monad m]
@[grind] class IndependentStates [MonadStateOf σ₁ m] [MonadStateOf σ₂ m]  : Prop where
  set_right_get_left_comm (s₂ : σ₂) :
    (do set s₂; MonadStateOf.get (m:=m)) = (MonadStateOf.get : m σ₁) >>= fun s₁ => set s₂ >>= fun _ => pure s₁
  set_left_get_right_comm (s₁ : σ₁) :
    (do set s₁; MonadStateOf.get : m σ₂) = MonadStateOf.get >>= fun s₂ => set s₁ >>= fun _ => pure s₂
  set_set_comm (s₁ : σ₁) (s₂ : σ₂) :
    (do set s₁; set s₂ : m PUnit) = (do set s₂; set s₁)

variable [LawfulMonad m]
instance : IndependentStates σ₁ σ₂ (StateT σ₁ (StateT σ₂ m)) where
  set_right_get_left_comm s₂ := by
    mysimp
  set_left_get_right_comm s₁ := by
    mysimp
  set_set_comm s₁ s₂ := by mysimp


end

export IndependentStates (set_right_get_left_comm)
export IndependentStates (set_left_get_right_comm)
export IndependentStates (set_set_comm)

section

variable (σ₁ σ₂ : Type) (m : Type → Type)
variable [Monad m] [LawfulMonad m] [MonadStateOf σ₁ m] [MonadStateOf σ₂ m] [IndependentStates σ₁ σ₂ m]

instance : IndependentStates σ₂ σ₁ m where
  set_right_get_left_comm s₂ := by grind
  set_left_get_right_comm s₁ := by grind
  set_set_comm s₁ s₂ := by grind


@[simp] theorem set_set_get {β} [LawfulMonadStateOf σ₁ m] (x : σ₁) (y : σ₂) (k : σ₁ → m β) :
  (do set (x : σ₁); set y; let x_1 ← getThe σ₁; k x_1) = (do set x; set y; k x) := by
  conv =>
    lhs
    conv =>
      rhs
      conv => rw [←bind_assoc, set_left_get_right_comm]
  simp
omit [LawfulMonad m] in
@[simp] theorem set_getThe {β} [LawfulMonadStateOf σ₁ m] (x : σ₁) (k : σ₁ → m β) :
  (do set (x : σ₁); let x_1 ← getThe σ₁; k x_1) = (do set x; k x) := by
    simp



-- omit [LawfulMonad m] in
-- theorem set_set_comm' (s₁ : σ₁) (s₂ : σ₂) :
--     (do set s₂; set s₁) = (do set s₁; set s₂ : m PUnit) := by
--     symm; apply set_set_comm

theorem set_set_swap (s₁ : σ₁) (s₂ : σ₂) (mx : m α) :
    (do set s₁; set s₂; mx) = (do set s₂; set s₁; mx) := by
    simp [←bind_assoc, set_set_comm]

@[simp]theorem set_set_set [LawfulMonadStateOf σ₁ m] [LawfulMonadStateOf σ₂ m] (s₁ : σ₁) (s₂ : σ₂) (s₃ : σ₁) (mx : m α) :
  (do set (m:=m) s₁; set (m:=m) s₂; set (m:=m) s₃; mx) = (do set s₂; set s₃; mx) := by
    conv =>
      lhs
      rw [←bind_assoc, set_set_comm]
    simp




end

instance [ToString α] : ToString (Thunk α) where
  toString a := toString a.get

instance [Inhabited α] : Inhabited (Thunk α) where
  default := Thunk.pure default



-- syntax "lazysimp" : tactic
-- macro_rules
-- | `(tactic | lazysimp) =>
--   `(tactic | simp_all only [set_set_get])










-- abbrev StrictLazyStateT (m : Type → Type) (σ₁ σ₂ δ : Type) := StateT σ₁ (LazyStateT σ₂ m) δ

-- instance {m : Type → Type} [Monad m] : MonadStateOf (σ₁ × σ₂) (StrictLazyStateT m σ₁ σ₂) where
--   get := do
--     let s₁ ← getThe σ₁
--     let s₂ ← getThe σ₂
--     return (s₁, s₂)

--   -- Decompose the setter
--   set := fun (s₁, s₂) => do
--     set s₁
--     set s₂

--   -- Define modifyGet to route correctly
--   modifyGet f := do
--     let s₁ ← getThe σ₁
--     let s₂ ← getThe σ₂
--     let (res, (news₁, news₂)) := f (s₁, s₂)
--     set news₁
--     set news₂
--     return res

-- instance {m σ₁ σ₂} [Monad m] : LazyMonadStateOf σ₂ (StrictLazyStateT m σ₁ σ₂) where
--   -- 1. Lift the standard State operations
--   get := StateT.lift get
--   set s := StateT.lift (set s)
--   modifyGet f := StateT.lift (modifyGet f)

--   -- 2. Lift the Lazy operation
--   -- We pass the function 'f' down to the inner monad to be thunked
--   lazyModify f := StateT.lift (lazyModify f)

-- syntax "lazy_simp" : tactic
-- local macro_rules
-- | `(tactic | lazy_simp) =>
--   `(tactic | simp_all (config := {singlePass := true}) only [get, getThe, MonadStateOf.get, StateT.run, pure, StateT.pure, StateT.bind, bind, modifyGet, MonadStateOf.modifyGet, StateT.get, map_eq_pure_bind, liftM, set, StateT.set, monadLift, MonadLift.monadLift, StateT.lift, Thunk.pure, Thunk.get, Thunk.map, lazyModify, modify, LawfulMonadStateOf.modifyGet_eq] <;> simp
--    )

-- syntax "mysimp" : tactic
-- local macro_rules
-- | `(tactic | mysimp) =>
--   `(tactic |
--     {
--     apply StateT.ext
--     intro s₁
--     apply StateT.ext
--     intro s₂
--     lazy_simp
--     }
--   )

-- instance {m} [Monad m] [LawfulMonad m] : LawfulMonadStateOf (σ₁ × σ₂) (StrictLazyStateT m σ₁ σ₂) where
--   modifyGet_eq f := by mysimp
--   get_bind_const mx := by mysimp
--   get_bind_get_bind mx := by mysimp
--   get_bind_set_bind mx := by mysimp
--   set_bind_get s := by mysimp
--   set_bind_set s := by intro ⟨s₁, s₂⟩; mysimp
-- instance {m} [Monad m] [LawfulMonad m] : LawfulMonadStateOf (σ₂) (StrictLazyStateT m σ₁ σ₂) where
--   modifyGet_eq f := by mysimp
--   get_bind_const mx := by mysimp
--   get_bind_get_bind mx := by mysimp
--   get_bind_set_bind mx := by mysimp
--   set_bind_get s := by mysimp
--   set_bind_set s s_1 := by mysimp

-- open LawfulMonadStateOf in
-- instance [Monad m] [LawfulMonad m]
-- : LawfulLazyMonadStateOf σ₂ (StrictLazyStateT m σ₁ σ₂) where
--   lazyModify_eq f := by mysimp
