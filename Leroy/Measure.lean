import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Subframes

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def increasingly_filtered (s : Set (Nucleus X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w

def increasingly_filtered' (s : Set (Opens X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w


structure Measure where
  toFun : (Opens X) → NNReal
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Opens X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set (Opens X)), increasingly_filtered' s → toFun (sSup s) = iSup (fun (x : s) ↦ toFun x)


-- subframes???
noncomputable def Measure.caratheodory {m : @Measure X h} (a : Nucleus X) : NNReal :=
  sInf (m.toFun '' {u : (Opens X) | a ≤ u})

lemma preserves_sup (m : Measure) (X_n : Set (Nucleus X)) (h : increasingly_filtered X_n) : m.caratheodory (sSup X_n) = sSup (m.caratheodory '' X_n) := by
  simp [sSup, e_V_nucleus, Measure.caratheodory]
  apply le_antisymm
  sorry
  sorry
