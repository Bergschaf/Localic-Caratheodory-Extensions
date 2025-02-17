/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Nucleus

namespace Nucleus

variable {X : Type*} [Order.Frame X]
variable (s : Set (Nucleus X)) (x : X)
variable {ι : Type*} (f : ι → Nucleus X)
variable (m n : Nucleus X)

@[simp] theorem sSup_apply : sSup s x = ⨅ j ∈ upperBounds s, j x := rfl

@[simp] theorem iSup_apply : iSup f x = ⨅ j ∈ upperBounds (Set.range f), j x := rfl

@[simp] theorem sup_apply : (m ⊔ n) x = ⨅ j ∈ upperBounds {m, n}, j x := by
  rw [← sSup_pair, sSup_apply]

end Nucleus
