import Leroy.Closed_Sublocals
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]

def Sublocale.interior (x : Sublocale E) := sSup {z : Open E | z ≤ x}

def Sublocale.closure (x : Sublocale E) := sInf {z : Closed E | x ≤ z.sublocale}

noncomputable def Sublocale.rand (x : Sublocale E) := x.closure.sublocale ⊓ (complement x.interior)

def Sublocale.exterior (x : Sublocale E) := sSup {z : Open E | z.sublocale ⊓ x = ⊥}

/-
/--
Dependency: Leroy lemma 8
Leroy 1.10.1
-/
lemma closure_eq_compl_ext (x : Sublocale E) : x.closure.sublocale = complement (x.sublocale) := by
  rw [Nucleus.exterior, Nucleus.closure, Closed.nucleus]
  have h : ({ element := (sInf {z : Closed E | x ≤ z.nucleus}).element } : Open E)  = (sSup {z | z.nucleus ⊓ x = ⊥}) := by
    simp [sSup, sInf]
    apply le_antisymm
    . apply sSup_le_sSup
      simp only [Set.image_subset_iff]
      rw [@Set.setOf_subset]
      intro a h
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
      use ⟨a.element⟩
      simp only [and_true]
      sorry --wahrscheinlich leroy lemme 8
    . apply sSup_le_sSup
      simp only [Set.image_subset_iff]
      rw [@Set.setOf_subset]
      intro xi hxi
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
      use ⟨xi.element⟩
      simp only [and_true]
      sorry --wahrscheinlich wieder leroy lemme 8


  apply_fun complement at h
  exact h-/

/-
lemma rand_eq_compl_int_ext (x : Sublocale E) : x.rand = complement (x.interior ⊔ x.exterior) := by sorry

lemma int_rand_eq_closure (x : Sublocale E) : x.interior.sublocale ⊔ x.rand = x.closure.sublocale := by sorry

lemma ext_rand_eq_comp_int (x : Sublocale E) : ↑x.exterior ⊔ x.rand = complement (x.interior) := by sorry-/
