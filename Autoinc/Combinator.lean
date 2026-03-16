/-
A libray of operator combinators.
-/
import Autoinc.Operator
import Autoinc.Data.Product.Change
import Autoinc.Data.List.Change
import Autoinc.Partial


namespace Operator

variable {α β γ ρ Δα Δβ Δγ Δρ : Type}
variable [ToString α] [ToString β] [ToString γ] [ToString ρ]
variable [ToString Δα] [ToString Δβ] [ToString Δγ] [ToString Δρ]
variable {m : Type → Type} [Monad m]
def compose (op₁ : Operator α β Δα Δβ m)
            (op₂ : Operator β γ Δβ Δγ m)
  : Operator α γ Δα Δγ m where
  f a := do
    let mid ← op₁.f a
    op₂.f mid
  Δf := op₁.Δf >=> op₂.Δf

infixl: 60 " >>>> "=> compose

def compose₁ (op₁ : Operator α β Δα Δβ m)
             (op₂ : Operator (β × ρ) γ (ΔProd Δβ Δρ) Δγ m)
  : Operator (α × ρ) γ (ΔProd Δα Δρ) Δγ m where
  f | (a, p) => do op₂.f ((← op₁.f a), p)

  Δf | ._1 Δa => do
        let Δmid ← op₁.Δf Δa
        op₂.Δf $ ._1 Δmid
     | ._2 Δb => do op₂.Δf $ ._2 Δb
     | ._1_2 Δa Δb => do
        let Δmid ← op₁.Δf Δa
        op₂.Δf $ ._1_2 Δmid Δb

infixl: 60 " >>>>₁ "=> compose₁

def compose₂ (op₁ : Operator α β Δα Δβ m)
             (op₂ : Operator (ρ × β) γ (ΔProd Δρ Δβ) Δγ m)
  : Operator (α × ρ) γ (ΔProd Δα Δρ) Δγ m where
  f | (a, p) => do op₂.f (p, (← op₁.f a))
  Δf | ._1 Δa => do
      let Δmid ← op₁.Δf Δa
      op₂.Δf $ ._2 Δmid
     | ._2 Δb => do op₂.Δf $ ._1 Δb
     | ._1_2 Δa Δb => do
       let Δmid ← op₁.Δf Δa
       op₂.Δf $ ._1_2 Δb Δmid

infixl: 60 " >>>>₂ "=> compose₂


def par (op₁ : Operator α γ Δα Δγ m)
        (op₂ : Operator β ρ Δβ Δρ m)
  : Operator (α × β) (γ × ρ) (ΔProd Δα Δβ) (ΔProd Δγ Δρ) m where
  f | (a, b) => do pure (← op₁.f a, ← op₂.f b)
  Δf | ._1 Δa => do pure (._1 (← op₁.Δf Δa))
     | ._2 Δb => do pure (._2 (← op₂.Δf Δb))
     | ._1_2 Δa Δb => do pure (._1_2 (← op₁.Δf Δa) (← op₂.Δf Δb))

infix: 60 " **** " => par

def toSeq (op : Operator α β Δα Δβ m)
  : Operator α β (List Δα) (List Δβ) m where
  f := op.f
  Δf := List.mapM op.Δf

variable {n : Type → Type} [Monad n]
def mapMonad (map : ∀ {x}, m x → n x)
  (op : Operator α β Δα Δβ m) : Operator α β Δα Δβ n where
  f x := map (op.f x)
  Δf Δx := map (op.Δf Δx)

def lift [MonadLiftT m n] (op : Operator α β Δα Δβ m) : Operator α β Δα Δβ n :=
  op.mapMonad liftM

end Operator


namespace PartialOperator
variable {m : Type → Type} [Monad m]
variable {α β γ Δα Δβ Δγ : Type}
def toSeq₁ (op : PartialOperator α β γ Δα Δβ Δγ m) : PartialOperator α β γ (List Δα) Δβ (List Δγ) m where
  f := op.f
  δf_1 da := da.mapM op.δf_1
  δf_2 db := do let dy ← op.δf_2 db; pure [dy]

def toSeq₂ (op : PartialOperator α β γ Δα Δβ Δγ m) : PartialOperator α β γ Δα (List Δβ) (List Δγ) m where
  f := op.f
  δf_1 da := do let dy ← op.δf_1 da; pure [dy]
  δf_2 db := db.mapM op.δf_2
def mapMonad {n : Type → Type} [Monad n] (map : ∀ {x}, m x → n x)
  (op : PartialOperator α β γ Δα Δβ Δγ m) : PartialOperator α β γ Δα Δβ Δγ n where
  f x y := map (op.f x y)
  δf_1 Δx := map (op.δf_1 Δx)
  δf_2 Δy := map (op.δf_2 Δy)
end PartialOperator

-- 1. TYPE TAGS
-- A thin wrapper that creates unique types for each layer (0, 1, 2...)





section
structure Lens (σ α : Type) where
  get : σ → α
  set : σ → α → σ

def zoom [Monad m] (lens : Lens σ α) (action : StateT α m β) : StateT σ m β := do
  let a ← get
  let (b, a') ← action.run (lens.get a)
  set (lens.set (← get) a')
  pure b
end

-- structure Lens.spec (lens : Lens σ α) where
--   get_set_law : ∀ (s : σ) (a : α), lens.get (lens.set s a) = a := by grind
--   set_get_law : ∀ (s : σ), lens.set s (lens.get s) = s := by grind

-- def zoom [Monad m] (lens : Lens σ α) (action : StateT α m β) : StateT σ m β := do
--   let a ← get
--   let (b, a') ← action.run (lens.get a)
--   set (lens.set (← get) a')
--   pure b
-- end

section
/-
α : Input type
β : Output type
Δα : Input change type
Δβ : Output change type
-/
variable {α β Δα Δβ : Type}
/-
σ : local state
τ : global state
-/
variable {σ τ : Type}

variable (m : Type → Type) [Monad m]
variable (lens : Lens τ σ)
/-
Given a stateful operator which uses a local state `s : σ`,
lift it to use a global state `t : τ `
-/
def Operator.zoomStateT (op : Operator α β Δα Δβ (StateT σ m)) (lens : Lens τ σ) : Operator α β Δα Δβ (StateT τ m) where
  f x := zoom lens (op.f x)
  Δf Δx := zoom lens (op.Δf Δx)

variable {γ Δγ : Type}

def PartialOperator.zoomStateT (op : PartialOperator α β γ Δα Δβ Δγ (StateT σ m)) (lens : Lens τ σ) : PartialOperator α β γ Δα Δβ Δγ (StateT τ m) where
  f x y := zoom lens (op.f x y)
  δf_1 Δx := zoom lens (op.δf_1 Δx)
  δf_2 Δy := zoom lens (op.δf_2 Δy)

def buildLensPair_1 : Lens (α × β) α where
  get s := s.1
  set s a := (a, s.2)

def buildLensPair_2 : Lens (α × β) β where
  get s := s.2
  set s a := (s.1, a)


end

namespace StructProd2

structure T (α β : Type) where
  _1 : α
  _2 : β
deriving Inhabited, Repr, BEq

variable {α β : Type}

def Lens₀ : Lens (T α β) α := ⟨fun s => s.1, fun ⟨_, s₁⟩ a => ⟨a, s₁⟩⟩
def Lens₁ : Lens (T α β) β := ⟨fun s => s.2, fun ⟨s₁, _⟩ a => ⟨s₁, a⟩⟩

end StructProd2


namespace StructProd3

structure T (α β γ : Type) where
  _1 : α
  _2 : β
  _3 : γ
deriving Inhabited, Repr, BEq


variable {α β γ : Type}
def Lens₀ : Lens (T α β γ) α := ⟨(·.1), fun s a => { s with _1 := a }⟩
def Lens₁ : Lens (T α β γ) β := ⟨(·.2), fun s a => { s with _2 := a }⟩
def Lens₂ : Lens (T α β γ) γ := ⟨(·.3), fun s a => { s with _3 := a }⟩

end StructProd3

namespace StructProd4

structure T (α β γ δ : Type) where
  _1 : α
  _2 : β
  _3 : γ
  _4 : δ
deriving Inhabited, Repr, BEq


variable {α β γ δ : Type}
def Lens₀ : Lens (T α β γ δ) α := ⟨(·.1), fun s a => { s with _1 := a }⟩
def Lens₁ : Lens (T α β γ δ) β := ⟨(·.2), fun s a => { s with _2 := a }⟩
def Lens₂ : Lens (T α β γ δ) γ := ⟨(·.3), fun s a => { s with _3 := a }⟩
def Lens₃ : Lens (T α β γ δ) δ := ⟨(·.4), fun s a => { s with _4 := a }⟩

end StructProd4


namespace StructProd5

structure T (α β γ δ ε : Type) where
  _1 : α
  _2 : β
  _3 : γ
  _4 : δ
  _5 : ε
deriving Inhabited, Repr, BEq


variable {α β γ δ ε : Type}
def Lens₀ : Lens (T α β γ δ ε) α := ⟨(·.1), fun s a => { s with _1 := a }⟩
def Lens₁ : Lens (T α β γ δ ε) β := ⟨(·.2), fun s a => { s with _2 := a }⟩
def Lens₂ : Lens (T α β γ δ ε) γ := ⟨(·.3), fun s a => { s with _3 := a }⟩
def Lens₃ : Lens (T α β γ δ ε) δ := ⟨(·.4), fun s a => { s with _4 := a }⟩
def Lens₄ : Lens (T α β γ δ ε) ε := ⟨(·.5), fun s a => { s with _5 := a }⟩

end StructProd5

namespace StructProd6

structure T (α β γ δ ε ζ : Type) where
  _1 : α
  _2 : β
  _3 : γ
  _4 : δ
  _5 : ε
  _6 : ζ
deriving Inhabited, Repr, BEq


variable {α β γ δ ε ζ : Type}
def Lens₀ : Lens (T α β γ δ ε ζ) α := ⟨(·.1), fun s a => { s with _1 := a }⟩
def Lens₁ : Lens (T α β γ δ ε ζ) β := ⟨(·.2), fun s a => { s with _2 := a }⟩
def Lens₂ : Lens (T α β γ δ ε ζ) γ := ⟨(·.3), fun s a => { s with _3 := a }⟩
def Lens₃ : Lens (T α β γ δ ε ζ) δ := ⟨(·.4), fun s a => { s with _4 := a }⟩
def Lens₄ : Lens (T α β γ δ ε ζ) ε := ⟨(·.5), fun s a => { s with _5 := a }⟩
def Lens₅ : Lens (T α β γ δ ε ζ) ζ := ⟨(·.6), fun s a => { s with _6 := a }⟩

end StructProd6
