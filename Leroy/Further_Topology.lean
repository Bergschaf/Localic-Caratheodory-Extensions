import Leroy.Closed_Sublocals
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]

def Nucleus.interior (x : Nucleus E) := sSup {z : Open E | z ≤ x}

def Nucleus.closure (x : Nucleus E) := sInf {z : Closed E | x ≤ z.nucleus}

def Nucleus.rand (x : Nucleus E) := x.closure.nucleus ⊓ (complement x.interior)

def Nucleus.exterior (x : Nucleus E) := sSup {z : Open E | z.nucleus ⊓ x = ⊥}


/--
Dependency: Leroy lemma 8
Leroy 1.10.1
-/
lemma closure_eq_compl_ext (x : Nucleus E) : x.closure.nucleus = complement (x.exterior) := by
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
  exact h

lemma rand_eq_compl_int_ext (x : Nucleus E) : x.rand = complement (x.interior ⊔ x.exterior) := by sorry

lemma int_rand_eq_closure (x : Nucleus E) : x.interior.nucleus ⊔ x.rand = x.closure.nucleus := by sorry

lemma ext_rand_eq_comp_int (x : Nucleus E) : ↑x.exterior ⊔ x.rand = complement (x.interior) := by sorry
