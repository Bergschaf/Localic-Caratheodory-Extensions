import Leroy.Nucleus
import Mathlib.Order.Synonym
import Mathlib.Tactic.ApplyFun
variable {E : Type*} [Order.Frame E]


abbrev Sublocale (E : Type*) [Order.Frame E] := (Nucleus E)ᵒᵈ

open Nucleus

instance : FunLike (Sublocale E) E E where
  coe x := x.toFun
  coe_injective' f g h := (by cases f;cases g; simp_all)

@[ext]
lemma ext (a b : Sublocale E) (h : ∀ x, a x = b x) : a = b := by
  exact Nucleus.ext h

lemma Sublocale.sup_apply (u v : Sublocale E) (x : E) : (u ⊔ v) x = u x ⊓ v x := by
  simp [OrderDual.instSup]
  rw [Nucleus.inf_apply]

lemma Nucleus.sup_apply (n m : Nucleus E) (x : E) : (n ⊔ m) x = ⨅ j, ⨅ (_ : n ≤ j ∧ m ≤ j), j x := by
  simp_rw [← sSup_pair, sSup_apply]
  simp

lemma Sublocale.min_apply (u v : Sublocale E) (x : E) : (u ⊓ v) x = ⨅ j, ⨅ (_ : j ≤ u ∧ j ≤ v), j x := by
  simp [OrderDual.instInf]
  rw [Nucleus.sup_apply]
  exact rfl



@[ext]
structure Open (E : Type*) [Order.Frame E] where
  element : E

namespace Open

protected def toSublocale (U : Open E) : Sublocale E where
  toFun x := U.element ⇨ x
  map_inf' x y := himp_inf_distrib U.element x y
  idempotent' x := by simp
  le_apply' x := by simp

instance : Coe (Open E) E where
  coe x := x.element

instance : Coe (Open E) (Sublocale E) where
  coe x := x.toSublocale

@[simp] lemma toSublocale_apply (U : Open E) (x : E) : U.toSublocale x = U.element ⇨ x := rfl

@[simp] lemma apply_self (U : Open E) : U.toSublocale U.element = ⊤ := by simp

lemma le_iff (U V : Open E) : U.toSublocale ≤ V.toSublocale ↔ U.element ≤ V.element := by
  apply Iff.intro
  . intro h
    simp [LE.le, Open.toSublocale] at h
    let h1 := h V.element
    simp at h1
    exact h1
  . intro h
    simp [LE.le]
    intro i
    repeat rw [toSublocale_apply] -- why does simp not work
    exact himp_le_himp_right h

lemma preserves_inf (U V : Open E) : U.toSublocale ⊓ V.toSublocale = (⟨U.element ⊓ V.element⟩ : Open E) := by
  sorry
