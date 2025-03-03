import Leroy.Sublocale
import Mathlib.Order.CompleteSublattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]
open Sublocale
def Sublocale.Open_Neighbourhood (u : Sublocale X) : Set (Open X) := {v : Open X | u ≤ v}

def Sublocale.Neighbourhood (u : Sublocale X) : Set (Sublocale X) := {v | ∃ w ∈ Open_Neighbourhood u, w ≤ v}


lemma Sublocale.Neighourhood.le {a : Sublocale E} : ∀ x ∈ Neighbourhood a, a ≤ x := by
  intro x h
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_setOf_eq] at h
  rcases h with ⟨w, ⟨h1,h2⟩⟩
  exact Preorder.le_trans a w.toSublocale x h1 h2

lemma Sublocale.Open_Neighbourhood.top_mem {x : Sublocale X}: ⊤ ∈ Open_Neighbourhood x := by
  simp [Open_Neighbourhood]

lemma Sublocale.Open_Neighbourhood.Nonempty (x : Sublocale X) : (Open_Neighbourhood x).Nonempty := by
  use ⊤
  exact top_mem

lemma Sublocale.Nonempty_Open_Neighbourhood (x : Sublocale X) : Nonempty (Open_Neighbourhood x) := by
  use ⊤
  exact Open_Neighbourhood.top_mem

-- TODO restliche Neighbourhood lemmas
lemma Sublocale.Neighbourhood.top_mem (x : Sublocale X) : ⊤ ∈ Neighbourhood x := by
  simp [Neighbourhood]
  use ⊤
  exact Open_Neighbourhood.top_mem

lemma Sublocale.Nonempty_Neighbourhood (x : Sublocale X) : Nonempty (Neighbourhood x) := by
  use ⊤
  exact Neighbourhood.top_mem x

lemma Sublocale.Open_Neighbourhood.inf_closed {x : Sublocale E} : ∀ U ∈ Open_Neighbourhood x, ∀ V ∈ Open_Neighbourhood x, U ⊓ V ∈ Open_Neighbourhood x := by
  simp [Open_Neighbourhood]
  intro U h1 V h2
  rw [Open.preserves_inf]
  exact le_inf h1 h2

lemma Sublocale.Neighbourhood.inf_closed (x : Sublocale E) : ∀ U ∈ Neighbourhood x, ∀ V ∈ Neighbourhood x, U ⊓ V ∈ Neighbourhood x := by
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_setOf_eq, le_inf_iff, forall_exists_index,
    and_imp, OrderDual.forall]
  intro a x1 h1 h2 n x2 h3 h4
  use x1 ⊓ x2
  simp_all only [Open.preserves_inf, le_inf_iff, and_self, true_and]
  apply And.intro
  . exact inf_le_of_left_le h2
  . exact inf_le_of_right_le h4

/-!
Properties of Complement
-/

/--
Leroy Lemme 8
-/
lemma sup_eq_top_iff_compl_le (V : Open E) (x : Sublocale E) : V.toSublocale ⊔ x = ⊤ ↔ V.compl ≤ x := by
  apply Iff.intro
  . intro h
    simp [Open.compl, Closed.toSublocale, complement, Sublocale.le_iff, Open.toSublocale] at *
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk] at *
    rw [Nucleus.ext_iff] at h
    conv at h =>
      enter [i]
      rw [Sublocale.top_apply, Sublocale.sup_apply, Nucleus.coe_mk, InfHom.coe_mk]
    intro i
    ----
    let h3 := h (i ⊔ V.element)
    simp at h3
    rw [sup_comm]
    rw [← h3]
    simp only [le_inf_iff, le_himp_iff]
    apply And.intro
    . exact inf_le_of_right_le le_sup_right
    . exact x.monotone le_sup_left
  . intro h
    rw [eq_top_iff]
    have h1 : V.toSublocale ⊔ V.compl.toSublocale ≤ V.toSublocale ⊔ x := by
     exact sup_le_sup_left h V.toSublocale
    apply le_trans' h1
    rw [@Open.sup_compl_eq_top]


lemma inf_eq_bot_iff_le_compl (V : Open E) (x : Sublocale E) : V.toSublocale ⊓ x = ⊥ ↔ x ≤ V.compl := by
  apply Iff.intro
  . intro h
    simp [Open.compl, Closed.toSublocale, complement, Sublocale.le_iff, Open.toSublocale] at *
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk] at *
    rw [Nucleus.ext_iff] at h

    conv at h =>
      enter [i]
      rw [Sublocale.bot_apply, Sublocale.inf_apply]
    simp [lowerBounds] at h
    conv at h =>
      enter [i, i]
      rw [Sublocale.le_iff, Nucleus.coe_mk, InfHom.coe_mk]
    intro i
    sorry


  . intro h
    have h1 : V.toSublocale ⊓ x ≤ V.toSublocale ⊓ V.compl := by
      exact inf_le_inf_left V.toSublocale h
    rw [eq_bot_iff]
    apply le_trans h1
    rw [@Open.inf_compl_eq_bot]


/--
Leroy Lemme 8 bis
-/
lemma sup_compl_eq_top_iff {x : Sublocale E} {u : Open E} : u ≤ x ↔ x ⊔ (u.compl) = ⊤ := by
  apply Iff.intro
  . intro h
    apply le_antisymm
    . apply BoundedOrder.toOrderTop.le_top
    .
      have h1 : u.toSublocale ⊔ u.compl.toSublocale ≤  x ⊔ u.compl.toSublocale := by
        exact sup_le_sup_right h u.compl.toSublocale
      apply le_trans' h1
      rw [Open.sup_compl_eq_top]
  . intro h
    rw [Nucleus.ext_iff] at h
    rw [Sublocale.le_iff]
    intro i
    let h1 := h i
    rw [Sublocale.sup_apply, Sublocale.top_apply] at h1

    simp [Open.compl,Closed.toSublocale, complement] at h1
    rw [Nucleus.coe_mk, InfHom.coe_mk] at h1
    rw [inf_sup_left] at h1
    simp [Open.toSublocale]
    rw [Nucleus.coe_mk, InfHom.coe_mk]
    simp only [le_himp_iff]
    apply le_trans' (le_of_eq h1)
    simp


lemma inf_compl_eq_bot_iff {x : Sublocale E} {u : Open E} : x ≤ u ↔ x ⊓ (u.compl) = ⊥ := by
  apply Iff.intro
  . intro h
    apply le_antisymm
    .
      apply_fun (fun x ↦ x ⊓ u.compl.toSublocale) at h
      dsimp at h
      rw [Open.inf_compl_eq_bot] at h
      exact h
      simp only [Monotone, le_inf_iff, inf_le_right, and_true, OrderDual.forall,
        OrderDual.toDual_le_toDual]
      exact fun a a_1 a_2 => inf_le_of_left_le a_2
    . exact OrderBot.bot_le (x ⊓ u.compl.toSublocale)
  .
    intro h i
    rw [Nucleus.ext_iff] at h

    simp [Open.compl, Closed.toSublocale, complement] at h
    conv at h =>
      enter [2]
      rw [Sublocale.inf_apply]
      rw [Sublocale.bot_apply]

    simp [Sublocale.le_iff, Sublocale.bot_apply] at h


    rw [Nucleus.coe_mk, InfHom.coe_mk] at h
    let h1 := h i x
    simp at h1
    sorry









lemma compl_sup_eq_inf_compl {U V : Open E} : (U ⊔ V).compl = U.compl ⊓ V.compl := by
  apply_fun ((fun x ↦ ↑x) : Closed E → Sublocale E)
  simp [Open.compl,Closed.toSublocale, complement]
  ext x
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp  [Closed.inf_def,Open.sup_def]
  --
  exact injective_of_le_imp_le (fun (x : Closed E) => x.toSublocale) fun {x y} a => (by exact (Closed.le_iff x y).mpr a)



/-!
Definitions
-/


def Sublocale.interior (x : Sublocale E) := sSup {z : Open E | z ≤ x}
lemma Open_interior_eq_id : ∀ a : Open E, a.toSublocale.interior = a := by
  simp only [Sublocale.interior]
  intro a
  apply le_antisymm
  . simp only [sSup_le_iff, Set.mem_setOf_eq]
    exact fun b a_1 => Open.le_iff.mpr a_1
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

lemma Open.inf_Exterior_eq_bot (x : Open E) : x ⊓ x.exterior = ⊥ := by
  simp [Open.exterior]
  ext
  simp [Open.inf_def,Open.sSup_def]
  rw [inf_sSup_eq]
  simp only [Set.mem_image, Set.mem_setOf_eq, iSup_exists]
  apply le_antisymm
  . simp [iSup_le]
    intro a h
    rw [inf_comm]
    rw [Open.ext_iff] at h
    exact h
  . exact OrderBot.bot_le _

/-
lemma Open.exterior_exterior_eq_self (x : Open E) : x.exterior.exterior = x := by
  simp [Open.exterior]
  rw [@sSup_eq_iSup']
  sorry
--/

--lemma Open.compl_le_exterior_iff {U V : Open E} : U.compl ≤ V.exterior.toSublocale ↔ V.closure ≤ U.toSublocale := by sorry

--lemma Open.exterior_compl_eq_self {U : Open E} : U.compl.exterior = U := by sorry

--lemma Open.exterior_inf_eq_sup {U V : Open E} : (U ⊓ V).exterior = U.exterior ⊔ V.exterior := by sorry


lemma Closure_compl_eq_exterior (U : Open E) : U.closure.compl = U.exterior := by
  ext
  simp [Open.closure, Closed.toSublocale, Closed.sInf_def, Closed.compl, Open.exterior, complement, Open.sSup_def, Open.toSublocale, Sublocale.le_iff]
  conv =>
    enter [1, 1, 2, 1, z, i]
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  apply le_antisymm
  . simp only [le_himp_iff, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h1 c h2
    let h3 := h2 ⊥
    simp at h3
    let h4 := h1 ⟨c.element⟩
    simp [Open.inf_def, h3, Open.ext_iff] at h4
    exact h4
  . simp only [le_himp_iff, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h a ha
    have h_help : (∀ (i : E), (a.element ⊔ i) ⊓ U.element ≤ i)  := by
      intro i
      rw [@inf_sup_right]
      simp [Open.inf_def, Open.ext_iff] at ha
      simp [ha]
    exact h ⟨a.element⟩ h_help


lemma Sublocale.compl_element_eq_compl_closure (V : Open E) : ⟨V.elementᶜ⟩ = V.closure.compl := by
  simp [Open.closure, Closed.compl, Closed.sInf_def]
  rw [← himp_bot, himp_eq_sSup]
  apply le_antisymm
  . simp only [le_bot_iff, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h1 b1 h2
    have h4 :V.toSublocale ≤ (⟨b1⟩:Closed E).toSublocale := by
      simp [Closed.toSublocale, complement]
      rw [Sublocale.le_iff]
      intro i
      rw [Nucleus.coe_mk, InfHom.coe_mk]
      simp [Open.toSublocale]
      repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
      apply And.intro <;> simp [h2]
    exact h1 ⟨b1⟩ h4
  . simp only [le_bot_iff, sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    simp [le_sSup_iff, upperBounds]
    intro b h1
    simp [Open.toSublocale, Closed.toSublocale, complement, Sublocale.le_iff] at h
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk] at h
    have h3 : a.element ⊓ V.element = ⊥ := by
      let h2 := h ⊥
      simp at h2
      apply_fun (. ⊓ V.element) at h2
      simp at h2
      exact h2
      rw [Monotone]
      exact fun ⦃a b⦄ a_1 => inf_le_inf_right V.element a_1
    exact h1 h3


lemma Open.compl_element_eq_exterior (U : Open E) : ⟨U.elementᶜ⟩ = U.exterior := by
  rw [Sublocale.compl_element_eq_compl_closure]
  rw [@Closure_compl_eq_exterior]


/-
lemma Open_closed_compl_le_iff (u : Open E) (c : Closed E) : u ≤ c.toSublocale ↔ c.compl ≤ u.compl.toSublocale := by
  apply Iff.intro
  . intro h
    simp [Open.compl, Closed.compl, Open.toSublocale, Closed.toSublocale, complement, Sublocale.le_iff]
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
    simp [Open.compl, Closed.compl, Open.toSublocale, Closed.toSublocale, complement, Sublocale.le_iff] at h
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]  at h
    simp at h
    simp only [le_himp_iff]
    intro i


    rw [inf_sup_right]
    let h1 := h (i ⊓ u.element)
    rw [inf_sup_right] at h1
    simp at h1

    let h2 := h (i ⊓ c.element ⊓ u.element)
    simp at h2
    obtain ⟨h2, h3⟩ := h2
    simp at

-/







/-
Dependency: Leroy lemma 8
Leroy 1.10.1

lemma closure_eq_compl_ext (x : Sublocale E) : x.closure = x.exterior.compl := by
  simp [Sublocale.closure,Sublocale.exterior, Open.compl]
  sorry
-/

-- TODO woanders
lemma compl_element_le_compl (V : Open E) : (⟨V.elementᶜ⟩ : Open E) ≤ V.compl.toSublocale := by
  simp [Open.toSublocale, Closed.toSublocale, complement, Sublocale.le_iff]
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp [@inf_sup_right]

/--
Quelle: Johnstone Lemma C 1.1.17 (S. 485)
-/
lemma Sublocale.eq_intersection_open_closed (j : Sublocale E) : j = ⨅ a : E, (⟨a⟩ : Open E).toSublocale ⊔ (⟨j a⟩ : Closed E) := by
    simp [Open.toSublocale, Closed.toSublocale, complement]
    apply le_antisymm
    . simp only [le_iInf_iff, le_iff, sup_apply]
      intro i l
      repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
      rw [inf_sup_left]
      simp
      apply And.intro
      . have h2 : (i ⇨ l) ⊓ j i ≤ j (i ⇨ l) ⊓ j i := inf_le_inf j.le_apply (by rfl)
        apply le_trans h2
        rw [← Nucleus.map_inf]
        apply Nucleus.monotone
        simp
      . apply j.le_apply

    . simp [iInf_le_iff]
      intro a h
      intro i
      let h1 := h i i
      rw [Sublocale.sup_apply] at h1
      repeat rw [Nucleus.coe_mk, InfHom.coe_mk] at h1
      simp at h1
      exact h1.left


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
