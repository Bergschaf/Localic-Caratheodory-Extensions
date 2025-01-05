import Leroy.Closed_Sublocals
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]

def Closed.compl (x : Closed E) : Open E := ⟨x.element⟩
def Open.compl (x : Open E) : Closed E := ⟨x.element⟩

lemma Open.complement_eq (x : Open E) : x.compl = (complement x) := by
  exact rfl

def Sublocale.interior (x : Sublocale E) := sSup {z : Open E | z ≤ x}
lemma Open_interior_eq_id : ∀ a : Open E, a.toSublocale.interior = a := by
  simp only [Sublocale.interior]
  intro a
  apply le_antisymm
  . simp only [sSup_le_iff, Set.mem_setOf_eq]
    exact fun b a => a
  . apply le_sSup
    simp only [Set.mem_setOf_eq, le_refl]

def Open.interior (x : Sublocale E) := x
noncomputable def Closed.interior (x : Closed E) : Open E := x.toSublocale.interior

def Sublocale.closure (x : Sublocale E) : Closed E:= sInf {z : Closed E | x ≤ z}
def Open.closure (x : Open E) : Closed E :=  sInf {z : Closed E | x ≤ z.toSublocale}

noncomputable def Sublocale.rand (x : Sublocale E) : Sublocale E := x.closure ⊓ (complement x.interior)

def Sublocale.exterior (x : Sublocale E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}
def Open.exterior (x : Open E) := sSup {z : Open E | z ⊓ x = ⊥}

lemma inf_Exterior_eq_bot (x : Open E) : x ⊓ x.exterior = ⊥ := by
  simp [Open.exterior, Open_min, Open_sSup]
  ext
  simp only
  rw [inf_sSup_eq]
  simp only [Set.mem_image, Set.mem_setOf_eq, iSup_exists, Open.bot]
  apply le_antisymm
  . simp [iSup_le]
    intro a h
    rw [inf_comm]
    exact h
  . apply OrderBot.bot_le

lemma Open.exterior_exterior_eq_self (x : Open E) : x.exterior.exterior = x := by
  simp [Open.exterior]
  sorry
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
W

  apply_fun complement at h
  exact h-/

/-
lemma rand_eq_compl_int_ext (x : Sublocale E) : x.rand = complement (x.interior ⊔ x.exterior) := by sorry

lemma int_rand_eq_closure (x : Sublocale E) : x.interior.sublocale ⊔ x.rand = x.closure.sublocale := by sorry

lemma ext_rand_eq_comp_int (x : Sublocale E) : ↑x.exterior ⊔ x.rand = complement (x.interior) := by sorry-/
