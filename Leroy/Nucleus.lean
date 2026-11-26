/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Nucleus
public import Mathlib.Order.Sublocale
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Additional nucleus lemmas

Pointwise descriptions of suprema of nuclei used in the sublocale development.
-/

@[expose] public section

namespace Nucleus

variable {X : Type*} [Order.Frame X]
variable (s : Set (Nucleus X)) (x : X)
variable {ι : Type*} (f : ι → Nucleus X)
variable (m n : Nucleus X)

/-- The supremum of a set of nuclei acts pointwise as the meet over the values of the
nuclei on upper bounds. -/
@[simp] theorem sSup_apply : sSup s x = ⨅ j ∈ upperBounds s, j x := rfl

/-- The supremum of a family of nuclei acts pointwise as the meet over the values on upper
bounds of the family's range. -/
@[simp] theorem iSup_apply : iSup f x = ⨅ j ∈ upperBounds (Set.range f), j x := rfl

/-- The supremum of two nuclei acts pointwise as the meet over the values on upper bounds
of the pair. -/
@[simp] theorem sup_apply : (m ⊔ n) x = ⨅ j ∈ upperBounds {m, n}, j x := by
  rw [← sSup_pair, sSup_apply]

/-- The pointwise Heyting implication of a nucleus `n` by a fixed frame element `V`:
the map `a ↦ V ⇨ n a`.  It is again a nucleus and serves as the interpolating nucleus in
the characterisation of the closed complement of an open (Leroy, Lemme 8). -/
def openHimp (V : X) (n : Nucleus X) : Nucleus X where
  toFun a := V ⇨ n a
  map_inf' a b := by rw [n.map_inf, himp_inf_distrib]
  idempotent' a := by
    have h_step : n (V ⇨ n a) ≤ V ⇨ n a := by
      apply le_himp_iff.mpr
      calc
        n (V ⇨ n a) ⊓ V ≤ n (V ⇨ n a) ⊓ n V := inf_le_inf_left _ n.le_apply
        _ = n ((V ⇨ n a) ⊓ V) := n.map_inf.symm
        _ ≤ n (n a) := n.monotone himp_inf_le
        _ = n a := n.idempotent a
    calc
      V ⇨ n (V ⇨ n a) ≤ V ⇨ (V ⇨ n a) := himp_le_himp_left h_step
      _ = V ⇨ n a := by rw [himp_himp, inf_idem]
  le_apply' a := by
    apply le_himp_iff.mpr
    exact le_trans inf_le_left n.le_apply

/-- The pointwise Heyting implication nucleus lies below the original nucleus. -/
lemma openHimp_le (V : X) (n : Nucleus X) :
    (openHimp V n).toSublocale ≤ n.toSublocale := by
  rw [Nucleus.toSublocale_le_toSublocale]
  intro a
  exact le_himp_iff.mpr (inf_le_left : n a ⊓ V ≤ n a)

end Nucleus
