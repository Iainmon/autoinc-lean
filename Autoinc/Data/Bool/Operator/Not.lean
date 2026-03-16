import Autoinc.Change
import Autoinc.Monad
import Autoinc.Operator
import Autoinc.Data.Bool.Change

namespace Not

variable (m : Type → Type) [ChangeMonad m]

@[simp] def op : Operator Bool Bool ΔBool ΔBool m where
  f b := pure b.not
  Δf := pure

variable [LawfulChangeMonad m]

theorem valid : (op m).valid := by
  intro x dx h
  cases dx <;>
  simp only [Change.valid, op, map_pure, seq_pure] <;>
  grind only [LawfulChangeMonad]


theorem correct : (op m).correct := by
  intro x dx h; cases dx <;> simp only [op, Change.patch, Bool.not_not, map_pure, seq_pure]


def spec : (op m).spec where
  valid := valid m
  correct := correct m

end Not
