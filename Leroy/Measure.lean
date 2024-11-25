import Mathlib.Data.Real.Basic
import Leroy.Basic

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def increasingly_filtered (s : Set X) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w

structure Measure where
  toFun : X → NNReal
  empty : toFun ⊥ = 0
  mono : ∀ (U V : X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set X), increasingly_filtered s → toFun (sSup s) = iSup (fun (x : s) ↦ toFun x)

noncomputable def caratheodory (m : @Measure X h) (a : X) : NNReal :=
  sInf (m.toFun '' {u : X | a ≤ u})
