import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Subframes

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def increasingly_filtered (s : Set X) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w

/-
structure Measure where
  toFun : (Opens X) → NNReal
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Opens X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set X), increasingly_filtered s → toFun (sSup s) = iSup (fun (x : s) ↦ toFun x)


-- subframes???
noncomputable def caratheodory (m : @Measure X h) (a : Subframe X) : NNReal :=
  sInf (m.toFun '' {u : X | a ≤ u})-/
