import Leroy.Nucleus
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice
import Leroy.Subframes
open CategoryTheory

variable {X Y E F: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E] [Order.Frame F]


def e_U (U : E) (H : E) : E :=
  sSup {W : E | W ⊓ U ≤ H}

lemma e_U_idempotent (U : E) (H : E) : e_U U (e_U U H) = e_U U H := by
  simp [e_U]
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply sSup_le_iff.mpr
    simp
    intro b h
    have h1 : sSup {W | W ⊓ U ≤ H} ⊓ U ≤ H := by
      simp [sSup_inf_eq]

    apply le_sSup
    simp
    apply_fun (. ⊓ U) at h
    dsimp at h
    let h3:= le_trans h h1
    simp at h3
    exact h3
    rw [Monotone]
    intro a b h
    exact inf_le_inf_right U h


  . apply sSup_le_iff.mpr
    simp
    intro b h
    apply le_sSup
    simp
    have h2 : H ≤ sSup {W | W ⊓ U ≤ H} := by
      apply le_sSup
      simp
    apply le_trans h h2

def e_U_increasing (U : E) (H : E) : H ≤ e_U U H := by
  simp only [e_U, Set.mem_setOf_eq, inf_le_left, le_sSup]

def e_U_preserves_inf (U: E) (H : E) (J : E) : e_U U (H ⊓ J) = e_U U H ⊓ e_U U J := by
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply le_inf_iff.mpr
    apply And.intro
    . simp [e_U]
      intro b h1 h2
      apply le_sSup
      simp [h1, h2]
    . simp [e_U]
      intro b h1 h2
      apply le_sSup
      simp [h1, h2]
  . simp [e_U, sSup_inf_sSup]
    intro a b h1 h2
    apply le_sSup
    simp_all only [Set.mem_setOf_eq]
    apply And.intro
    · have h3 : a ⊓ b ⊓ U ≤ a ⊓ U := by
        simp
        refine inf_le_of_left_le ?h
        exact inf_le_left
      apply le_trans h3 h1
    · have h3 : a ⊓ b ⊓ U ≤ b ⊓ U := by
        simp
        rw [inf_assoc]
        apply inf_le_of_right_le
        exact inf_le_left
      apply le_trans h3 h2

def eckig (U : E) : Nucleus E where
  toFun := e_U U
  idempotent := e_U_idempotent U
  increasing := e_U_increasing U
  preserves_inf := e_U_preserves_inf U



def is_open (e : Nucleus E) : Prop :=
  ∃ u : E, eckig u = e


-- TODO typeclass
--class Open extends Subframe E where
--  is_open : ∃ u : E, eckig u = e


def Opens (E : Type*) [Order.Frame E] := {e : Nucleus E // is_open e}

noncomputable def open_to_E (e : Opens E) : E :=
  Classical.choose e.prop

lemma eckig_open_to_E {e : Opens E} : (eckig (open_to_E e)) = e.val := by
  simp [open_to_E]
  let h := Classical.choose_spec e.prop
  exact h

instance Opens_le : LE (Opens E) where
  le x y := x.val ≤ y.val

instance : Bot (Opens E) where
  bot := ⟨⊥, (by simp[is_open];use ⊥; simp[eckig];ext x;simp[e_U, Nucleus_bot, sSup, e_V_nucleus, e_V];)⟩

instance Opens_top : Top (Opens E) where
  top := ⟨⊤, (by simp[is_open,Nucleus_top, eckig]; use ⊤; ext x; simp [e_U]; apply le_antisymm; apply sSup_le; simp only [Set.mem_setOf_eq, imp_self, implies_true]; apply le_sSup;simp)⟩

lemma opens_le_top : ∀ (U : Opens E), U ≤ ⊤ := by
  intro u
  simp_rw [Opens_top, Opens_le, Nucleus_top]
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe]
  intro v
  apply Nucleus.increasing'

instance : Coe (Opens E) (Nucleus E) where
  coe x := Subtype.val x

instance : Coe (Set (Opens E)) (Set (Nucleus E)) where
  coe x := Subtype.val '' x


-- Leroy Lemme 6


lemma leroy_6a (x : Nucleus E) (U : E) : x ≤ eckig U ↔ (x U = ⊤) := by
  apply Iff.intro
  . intro h
    simp[le] at h
    let h1 := h U
    have h2 : (eckig U) U = ⊤ := by
      simp [eckig, e_U]
    exact eq_top_mono (h U) h2
  . intro h
    simp [eckig, le]
    intro v
    simp [ e_U]
    intro b h1
    apply_fun x.toFun at h1
    rw [x.preserves_inf] at h1
    simp at h1
    rw [h] at h1
    simp at h1
    apply le_trans (x.increasing b) h1
    exact Nucleus.monotone x


lemma leroy_6b {U V : E} : e_U (U ⊓ V) = e_U U ∘ e_U V := by
  ext x
  simp [e_U]
  apply le_antisymm
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h
    apply le_sSup
    simp
    rw [inf_assoc]
    exact h
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h
    apply_fun (fun x ↦ x ⊓ V) at h
    dsimp at h
    have h1 : sSup {W | W ⊓ V ≤ x} ⊓ V ≤ x := by
      rw [sSup_inf_eq]
      simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
    rw [inf_assoc] at h
    exact Preorder.le_trans (a ⊓ (U ⊓ V)) (sSup {W | W ⊓ V ≤ x} ⊓ V) x h h1
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right V a_1

lemma e_U_comm {U V : E} : e_U U ∘ e_U V = e_U V ∘ e_U U := by
  ext x
  simp [e_U]
  apply le_antisymm
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h
    apply le_sSup
    simp
    apply_fun (fun x ↦ x ⊓ V) at h
    dsimp at h
    have h1 : sSup {W | W ⊓ V ≤ x} ⊓ V ≤ x := by
      rw [sSup_inf_eq]
      simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
    rw [inf_assoc]
    rw [inf_comm V U]
    rw [← inf_assoc]
    exact Preorder.le_trans (a ⊓ U ⊓ V) (sSup {W | W ⊓ V ≤ x} ⊓ V) x h h1
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right V a_1
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h
    apply le_sSup
    simp
    apply_fun (fun x ↦ x ⊓ U) at h
    dsimp at h
    have h1 : sSup {W | W ⊓ U ≤ x} ⊓ U ≤ x := by
      rw [sSup_inf_eq]
      simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
    rw [inf_assoc]
    rw [inf_comm U V]
    rw [← inf_assoc]
    exact Preorder.le_trans (a ⊓ V ⊓ U) (sSup {W | W ⊓ U ≤ x} ⊓ U) x h h1
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right U a_1

lemma eckig_preserves_inclusion {U V : E} : U ≤ V ↔ eckig U ≤ eckig V := by
  apply iff_iff_implies_and_implies.mpr
  apply And.intro
  . intro h
    simp [eckig, le, e_U]
    intro v b h1
    apply le_sSup
    simp
    have h2 : b ⊓ U ≤ b ⊓ V := by
      exact inf_le_inf_left b h
    exact Preorder.le_trans (b ⊓ U) (b ⊓ V) v h2 h1
  . intro h
    simp [eckig, le, e_U] at h
    let h1 := h V U
    simp at h1
    apply_fun (fun x ↦ x ⊓ U) at h1
    dsimp at h1
    have h2 : sSup {W | W ⊓ U ≤ V} ⊓ U ≤ V := by
      rw [sSup_inf_eq]
      simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
    have h3 : U ≤ U ⊓ U := by
      simp only [le_refl, inf_of_le_left]
    apply le_trans h3
    exact Preorder.le_trans (U ⊓ U) (sSup {W | W ⊓ U ≤ V} ⊓ U) V h1 h2
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right U a_1



lemma eckig_preserves_inf (U V : E) : eckig (U ⊓ V) = eckig U ⊓ eckig V := by
  apply le_antisymm
  . simp [eckig]
    simp only [min, sInf, sSup, e_V_nucleus, Set.mem_insert_iff, Set.mem_singleton_iff,
      Nucleus.le_iff, Nucleus.toFun_eq_coe, forall_eq_or_imp, Nucleus.toFun_eq_coe', forall_eq, e_V,
      Set.mem_setOf_eq, and_imp, Function.comp_apply, sSup_le_iff]
    have h_help : SemilatticeInf.inf U V = U ⊓ V := by
      rfl
    have h2 : (∀ (v : E), e_U U v ≤ (eckig (SemilatticeInf.inf U V)) v) := by
      simp [e_U, eckig]
      intro v b h1
      apply le_sSup
      simp
      have h :  b ⊓ SemilatticeInf.inf U V ≤ b ⊓ U := by
        rw [h_help]
        simp [← inf_assoc]
        apply And.intro
        · refine inf_le_of_left_le ?left.h
          exact inf_le_left
        · rw [inf_comm b U]
          apply inf_le_of_left_le
          exact inf_le_left
      apply Preorder.le_trans (b ⊓ SemilatticeInf.inf U V) (b ⊓ U) v h h1

    have h3 : (∀ (v : E), e_U V v ≤ (eckig (SemilatticeInf.inf U V)) v)  := by
      simp [e_U, eckig]
      intro v b h1
      apply le_sSup
      simp
      rw [h_help]
      have h : b ⊓ (U ⊓ V) ≤ b ⊓ V := by
        simp only [le_inf_iff, inf_le_left, true_and]
        rw [inf_comm U V]
        rw [← inf_assoc]
        apply inf_le_of_left_le
        exact inf_le_right
      exact Preorder.le_trans (b ⊓ (U ⊓ V)) (b ⊓ V) v h h1
    --let h1 := h (eckig (SemilatticeInf.inf U V)) h2 h3

    --simp [eckig] at h1
    exact ⟨h2, h3⟩

  . simp only [Nucleus_min, sInf, sSup, e_V_nucleus, Set.mem_insert_iff, Set.mem_singleton_iff,
    Nucleus.le_iff, Nucleus.toFun_eq_coe, forall_eq_or_imp, forall_eq, eckig, Nucleus.toFun_eq_coe',
    e_U, sSup_le_iff, Set.mem_setOf_eq, e_V, and_imp]
    intro v b h1
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    intro x_i h2 h3
    have h1_ : b ⊓ V ⊓ U ≤ v := by
      rw [inf_comm U V] at h1
      rw [← inf_assoc] at h1
      exact h1
    let h4 := h2 (v) (b ⊓ V) h1_
    let h5 := h3 (x_i v) (b) h4
    rw [Nucleus.idempotent'] at h5
    exact h5

lemma opens_inf_closed (U V : Opens X) : is_open (U.val ⊓ V.val) := by
  rw [is_open]
  let h1 := U.2
  let h2 := V.2
  simp [is_open] at h1 h2
  rcases h1 with ⟨u, h1⟩
  rcases h2 with ⟨v, h2⟩
  rw [← h1, ← h2]
  use u ⊓ v
  exact eckig_preserves_inf u v

instance : Min (Opens X) where
  min U V := ⟨U ⊓ V, opens_inf_closed U V⟩

lemma eckig_preserves_sup (U_i : Set X) : sSup (eckig '' U_i) = eckig (sSup U_i) := by
  ext x
  simp [eckig, sSup, e_V_nucleus, e_V, e_U]
  apply le_antisymm
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h
    have h1 : a ≤ sSup {W | W ⊓ sSup U_i ≤ x} := by
      apply le_sSup
      simp only [Set.mem_setOf_eq]
      rw [inf_sSup_eq]
      simp only [iSup_le_iff]
      intro i h1
      let h2 := h i h1
      apply_fun (fun x ↦ x ⊓ i) at h2
      dsimp at h2
      have h3 :sSup {W | W ⊓ i ≤ x} ⊓ i ≤ x := by
        rw [sSup_inf_eq]
        simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
      exact Preorder.le_trans (a ⊓ i) (sSup {W | W ⊓ i ≤ x} ⊓ i) x h2 h3
      rw [Monotone]
      exact fun ⦃a b⦄ a_1 => inf_le_inf_right i a_1
    apply_fun (fun x ↦ x ⊓ sSup U_i) at h1
    dsimp at h1
    have h2 : sSup {W | W ⊓ sSup U_i ≤ x} ⊓ sSup U_i ≤ x := by
      rw [sSup_inf_sSup]
      simp only [Set.mem_prod, Set.mem_setOf_eq, iSup_le_iff, and_imp, Prod.forall]
      intro b c h2 h3
      have h4 : b ⊓ c ≤ b ⊓ sSup U_i := by
        simp only [le_inf_iff, inf_le_left, true_and]
        refine inf_le_of_right_le ?h
        apply le_sSup
        exact h3
      exact Preorder.le_trans (b ⊓ c) (b ⊓ sSup U_i) x h4 h2
    exact Preorder.le_trans (a ⊓ sSup U_i) (sSup {W | W ⊓ sSup U_i ≤ x} ⊓ sSup U_i) x h1 h2
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right (sSup U_i) a_1

  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro a h a1 h1
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    have h2 : a ⊓ a1 ≤ a ⊓ sSup U_i := by
      simp
      refine inf_le_of_right_le ?h
      apply le_sSup
      exact h1
    exact Preorder.le_trans (a ⊓ a1) (a ⊓ sSup U_i) x h2 h




lemma opens_sSup_closed {U_i : Set (Opens X)} : is_open (sSup (Subtype.val '' U_i)) := by
  rw [is_open]
  have h1 : ∀ u_i ∈ U_i, is_open u_i.val := by
    intro u_i h
    exact u_i.2
  have h2 : ∃ U_i', (Subtype.val '' U_i) = eckig '' U_i' := by
    simp [is_open] at h1
    let h2 (u_i : Opens X) : X := by
      let h := u_i.prop
      simp [is_open] at h
      use Classical.choose h
    let h4 (u_i : Opens X) : eckig (h2 u_i) = u_i := by
      simp [h2]
      exact Set.apply_rangeSplitting eckig u_i
    use h2 '' U_i
    have h3 := fun (x : Opens X) ↦ h4 x
    simp_all only [implies_true, h2, h4]
    ext x : 1
    simp_all only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right, exists_exists_and_eq_and, h4]
    apply Iff.intro
    · intro a
      obtain ⟨w, h⟩ := a
      apply Exists.intro
      · apply And.intro
        · exact h
        · simp_all only
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only [Subtype.coe_eta, exists_prop, and_true]
      apply h1
      simp_all only

  rcases h2 with ⟨U_i', h2⟩
  rw [h2]
  use sSup U_i'
  exact Eq.symm (eckig_preserves_sup U_i')

lemma eckig_preserves_max (U V : X) : eckig (U ⊔ V) = (eckig U ⊔ eckig V) := by
  simp [Nucleus_max]
  have h : U ⊔ V = sSup {U, V} := by
    exact Eq.symm sSup_pair
  let x := eckig_preserves_sup {U, V}
  simp at x
  rw [← x]
  simp [Set.image]
  have h1 : {x | eckig U = x ∨ eckig V = x} = {eckig U, eckig V} := by
    ext x
    simp
    simp_all only [sSup_insert, csSup_singleton]
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [true_or]
      | inr h_1 =>
        subst h_1
        simp_all only [or_true]
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [true_or]
      | inr h_1 =>
        subst h_1
        simp_all only [or_true]
  rw [h1]


instance : SupSet (Opens X) where
  sSup U_i := ⟨sSup (Subtype.val '' U_i), opens_sSup_closed⟩

instance : Max (Opens X) where
  max U V := sSup {U, V}

lemma eckig_injective : Function.Injective (@eckig E e_frm)  := by
  rw [Function.Injective]
  . intro a1 a2 h
    rw [le_antisymm_iff] at h
    rcases h with ⟨h1, h2⟩
    apply le_antisymm
    . exact eckig_preserves_inclusion.mpr h1
    . exact eckig_preserves_inclusion.mpr h2




-- Ist hier das Inverse Image gemeint?
--lemma leroy_6d {f : FrameHom E F} {V : F} : f (eckig v) = eckig ((f_obenstern f).obj v) := by


/-
lemma leroy_7 {X : Opens E} {U V : E} : V ≤ X.val U ↔ eckig V ⊓ X ≤ eckig U := by
  let i := nucleus_frameHom X.val
  rw [i.prop.left]
  have h : (f_obenstern i.val ⋙ f_untenstern i.val).obj = (f_untenstern i.val).obj ∘ (f_obenstern i.val).obj := by
    exact rfl

  rw [h]

  ---
  have h1 :  V ≤ ((f_untenstern i.val).obj ∘ (f_obenstern i.val).obj) U ↔ (f_obenstern i.val).obj V ≤ (f_obenstern i.val).obj U := by
    have h (U V : E) {f : E → E}:  V ≤ f U ↔ (f_obenstern i.val).obj V ≤ (f_obenstern i.val).obj (f U) := by
      have h1 : Monotone (f_obenstern i.val).obj := by
        simp [Monotone, f_obenstern]
        exact fun ⦃a b⦄ a_1 => OrderHomClass.GCongr.mono (i.val) a_1
      have h2 : ∀ a b,(f_obenstern i.val).obj a ≤ (f_obenstern i.val).obj b → a ≤ b := by
        have h : ∀ a, (f_untenstern i.val).obj ((f_obenstern i.val).obj a) = a := by
          intro a
          simp [f_obenstern, f_untenstern]
          apply le_antisymm
          apply sSup_le
          simp
          intro b h

          sorry -- TODO i a ≤ i b → a ≤ b
          apply le_sSup
          simp

        intro a b h1
        apply_fun (f_untenstern i.val).obj at h1
        simp [h] at h1
        exact h1
        simp [Monotone, f_untenstern]
        intro a ha b hb h1 e h2
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        have h : (⟨a, ha⟩ : Image X) ≤ ⟨b, hb⟩ := by
          exact h1
        exact Preorder.le_trans (i.val e) ⟨a, ha⟩ ⟨b, hb⟩ h2 h1

      rw [Monotone] at h1
      exact { mp := @h1 V (f U), mpr := h2 V (f U) }

    apply Iff.trans (h U V)
    simp
    have h1 : (f_obenstern i.val).obj ((f_untenstern i.val).obj ((f_obenstern i.val).obj U)) = (f_obenstern i.val).obj U := by
      let x := triangle_one_obj i.val U
      simp at x
      exact x
    rw [h1]

  apply Iff.trans h1





instance : InfSet (Opens X) where
  sInf U_i := sSup {U : Opens X | ∀ u_i ∈ U_i, U ≤ u_i}
-/
