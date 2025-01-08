import Leroy.Closed_Sublocals
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]

/-!
Properties of Complement
-/
def Closed.compl (x : Closed E) : Open E := ⟨x.element⟩
def Open.compl (x : Open E) : Closed E := ⟨x.element⟩

lemma Open.complement_eq (x : Open E) : x.compl = (complement x) := by
  exact rfl

lemma Open.inf_compl {x : Open E} : x.toSublocale ⊓ x.compl = ⊥ := by
  rw [Open.complement_eq]
  exact inf_complement x

/--
Leroy Lemme 8 bis
-/
def sup_compl_eq_top_iff {x : Sublocale E} {u : Open E} : u ≤ x ↔ x ⊔ (u.compl) = ⊤ := by
  apply Iff.intro
  . intro h
    apply le_antisymm
    . exact OrderTop.le_top (x ⊔ u.compl.toSublocale)
    .
      have h1 : u.toSublocale ⊔ u.compl.toSublocale ≤  x ⊔ u.compl.toSublocale := by
        exact sup_le_sup_right h u.compl.toSublocale
      apply le_trans' h1
      rw [Open.complement_eq]
      rw [@sup_comp_eq_top]
  . intro h
    simp_rw [Sublocale.max_eq,sSup,sInf] at h
    simp [Sublocale.ext_iff, sInf_fun] at h
    simp [Sublocale.le_iff]
    intro v
    let h1 := h v
    have h2 : (⊤ : Sublocale E) v = v := by
      exact rfl
    rw [h2] at h1
    rw [Set.setOf_or] at h1
    simp [Open.compl,Closed.toSublocale, complement] at h1
    rw [@inf_sup_right] at h1
    --
    simp [Open.toSublocale, eckig, e_U]
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    let h3 := le_of_eq h1
    rw [@sup_le_iff] at h3
    rw [inf_comm]
    exact h3.left

def inf_compl_eq_bot_iff {x : Sublocale E} {u : Open E} : x ≤ u ↔ x ⊓ (u.compl) = ⊥ := by
  apply Iff.intro
  . intro h
    apply le_antisymm
    . apply_fun (fun x ↦ x ⊓ u.compl.toSublocale) at h
      dsimp at h
      rw [Open.inf_compl] at h
      exact h
      simp only [Monotone, le_inf_iff, inf_le_right, and_true, OrderDual.forall,
        OrderDual.toDual_le_toDual]
      exact fun a a_1 a_2 => inf_le_of_left_le a_2
    . exact OrderBot.bot_le (x ⊓ u.compl.toSublocale)
  .
    intro h
    sorry





/-!
Definitions
-/


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
def Closed.exterior (x : Closed E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}

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
  rw [@sSup_eq_iSup']
  sorry

lemma closure_eq_compl_exterior_compl : ∀ a : Open E, a.closure.toSublocale = a.exterior.compl.toSublocale := by
  sorry

lemma le_compl_iff {U V : Open E} : U.compl ≤ V.toSublocale ↔ V.compl ≤ U.toSublocale := by
  sorry

lemma compl_le_iff {U V : Open E} : U.compl ≤ V.exterior.toSublocale ↔ V.closure ≤ U.toSublocale := by sorry

lemma Open.exterior_compl_eq_self {U : Open E} : U.compl.exterior = U := by sorry

lemma Open.exterior_inf_eq_sup {U V : Open E} : (U ⊓ V).exterior = U.exterior ⊔ V.exterior := by sorry


/--
Dependency: Leroy lemma 8
Leroy 1.10.1
-/
lemma closure_eq_compl_ext (x : Sublocale E) : x.closure = x.exterior.compl := by
  simp [Sublocale.closure,Sublocale.exterior, Open.compl]

  apply le_antisymm
  .
    rw [Closed.le_iff]
    simp only [sSup, sInf, sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    ---
    apply le_sSup
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use a.compl
    apply And.intro
    . sorry
    . rfl
  .
    simp only [le_sInf_iff, Set.mem_setOf_eq]
    intro b h

    apply le_trans' h
    simp only [Closed.toSublocale]
    rw [complement]
    rw [Sublocale.le_iff]
    simp only [Nucleus.toFun_eq_coe]
    intro v
    simp only [sSup]
    rw [@sSup_image]
    simp only [Set.mem_setOf_eq]
    rw [iSup_sup]
    rw [le_iSup_iff]
    simp only [sup_le_iff, iSup_le_iff]
    intro b1 h1
    rw [Sublocale.le_iff] at h
    let h2 := h v
    let h3 := h1 (x.exterior)
    have h4 :  (x.exterior.toSublocale ⊓ x = ⊥)  := by
      sorry
    rcases h3 with ⟨h3, h6⟩
    let h5 := h3 h4
    sorry



/-
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
