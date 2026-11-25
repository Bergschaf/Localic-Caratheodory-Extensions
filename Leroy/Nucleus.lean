/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Nucleus
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

end Nucleus
