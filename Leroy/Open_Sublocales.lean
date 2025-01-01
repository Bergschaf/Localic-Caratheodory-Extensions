import Leroy.Nucleus
import Leroy.Sublocale
import Leroy.NucleusFrame

variable {X Y E F: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E] [Order.Frame F]


def e_U (U : E) (H : E) : E :=
  sSup {W : E | W ⊓ U ≤ H}

def e_U' (U H : E) : E := U ⇨ H

example : @e_U E e_frm = e_U' := by
  ext x y
  simp_rw [e_U, e_U']
  apply le_antisymm
  . apply sSup_le_iff.mpr
    simp only [Set.mem_setOf_eq, le_himp_iff, imp_self, implies_true]
  . apply le_sSup_iff.mpr
    simp [upperBounds]
    intro b h
    simp_all only [himp_inf_self, inf_le_left]


lemma e_U_idempotent (U : E) (H : E) : e_U U (e_U U H) ≤ e_U U H := by
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

def eckig (U : E) : Sublocale E where
  toFun := e_U U
  idempotent := e_U_idempotent U
  increasing := e_U_increasing U
  preserves_inf := e_U_preserves_inf U




-- TODO typeclass
--class Open extends Subframe E where
--  is_open : ∃ u : E, eckig u = e
@[ext]
structure Open (E : Type*) [Order.Frame E] where
  element : E

def Open.sublocale (x : Open E) :=  eckig x.element

instance : Coe (Open E) E where
  coe x := x.element

instance : Coe (Open E) (Sublocale E) where
  coe x := x.sublocale


def is_open (e : Sublocale E) : Prop :=
  ∃ u : E, eckig u = e


noncomputable def Nucleus_to_Open (e : Nucleus E) (h : is_open e) : Open E :=
  ⟨Classical.choose h⟩
-- Leroy Lemme 6

lemma Open_is_open (e : Open E) : is_open e.sublocale := by
  simp only [is_open, Open.sublocale, exists_apply_eq_apply]


lemma leroy_6a (x : Sublocale E) (U : E) : x ≤ eckig U ↔ (x U = ⊤) := by
  apply Iff.intro
  . intro h
    simp[Nucleus.le_iff] at h
    let h1 := h U
    have h2 : (eckig U) U = ⊤ := by
      simp only [eckig]
      rw [Nucleus.fun_of]
      simp only [e_U, inf_le_right, Set.setOf_true, sSup_univ]

    exact eq_top_mono (h U) h2
  . intro h
    simp [eckig, Nucleus.le]
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
    intro v
    simp [eckig, Nucleus.le, e_U]
    intro b h1
    apply le_sSup
    simp
    have h2 : b ⊓ U ≤ b ⊓ V := by
      exact inf_le_inf_left b h
    exact Preorder.le_trans (b ⊓ U) (b ⊓ V) v h2 h1
  . intro h

    simp [eckig,  e_U] at h
    simp [Sublocale.le_iff] at h

    let h1 := h V
    simp only at h1
    apply_fun (fun x ↦ x ⊓ U) at h1
    dsimp at h1
    have h2 : sSup {W | W ⊓ U ≤ V} ⊓ U ≤ V := by
      rw [sSup_inf_eq]
      simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]
    have h3 : U ≤ U ⊓ U := by
      simp only [le_refl, inf_of_le_left]
    apply le_trans h3
    apply le_trans' h2
    simp [e_U] at h1
    exact inf_le_inf_right U h1
    rw [Monotone]
    exact fun ⦃a b⦄ a_1 => inf_le_inf_right U a_1

@[simp]
lemma coe_to_dual {n : Nucleus E} {x : E}: (OrderDual.toDual n) x = n x := by rfl

lemma eckig_preserves_inf (U V : E) : eckig (U ⊓ V) = eckig U ⊓ eckig V := by
  apply le_antisymm
  . simp [eckig]
    simp only [min, sInf, sSup, Set.mem_insert_iff, Set.mem_singleton_iff,
      Nucleus.le_iff, Nucleus.toFun_eq_coe, forall_eq_or_imp, Nucleus.toFun_eq_coe, forall_eq, e_V,
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

  . simp [eckig, e_U]
    simp only [Sublocale.min_eq, sInf, sSup, Set.mem_insert_iff, Set.mem_singleton_iff,
      Sublocale.le_iff, Nucleus.toFun_eq_coe, forall_eq_or_imp, Nucleus.fun_of, e_U, sSup_le_iff,
      Set.mem_setOf_eq, forall_eq, sInf_fun, le_sInf_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro v b h1
    rw [Nucleus_mem_sublocale] at h1
    simp [Sublocale.nucleus] at h1
    intro b1 h2
    rcases h1 with ⟨h3, h4⟩

    have h1_ : b1 ⊓ U ⊓ V ≤ v := by
      rw [← inf_assoc] at h2
      exact h2

    let h4 := h4 (v) (b1 ⊓ U) h1_
    let h5 := h3 (b v) (b1) h4
    simp at h5
    rw [coe_to_dual] at h5
    rw [Nucleus.idempotent''] at h5
    exact h5

------------
lemma eckig_preserves_sSup (U_i : Set X) : sSup (eckig '' U_i) = eckig (sSup U_i) := by
  ext x
  simp only [eckig, Nucleus.toFun_eq_coe, Nucleus.fun_of]
  rw [← leroy_eq_stone]
  simp only [e_V_sublocale, Nucleus.fun_of, e_V, Set.mem_image, Nucleus.toFun_eq_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, e_U]
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

/--
lemma eckig_preserves_sInf (U_i : Set E) : sInf (eckig '' U_i) = eckig (sInf U_i) := by
  ext x
  simp only [sInf, sSup, eckig, Set.mem_image, Sublocale.le_iff, Nucleus.toFun_eq_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Nucleus.fun_of, e_U, sSup_le_iff,
    Set.mem_setOf_eq, sInf_fun]
  apply le_antisymm
  . apply le_sSup_iff.mpr
    simp [upperBounds]
    intro b h
    apply sInf_le_iff.mpr
    simp [lowerBounds]
    intro b1 h1
    sorry-/

lemma eckig_preserves_top : eckig (⊤ : E) = ⊤ := by
  ext x
  simp [eckig, e_U]
  rw [Sublocale.top_eq]
  refine IsLUB.sSup_eq ?_
  rw [IsLUB, IsLeast]
  simp [upperBounds, lowerBounds, Sublocale.top_eq]
  intro a h
  exact le_of_forall_le h

--def FrameHom_eckig : FrameHom E (Nucleus E) :=
--  ⟨⟨⟨eckig, eckig_preserves_inf⟩, eckig_preserves_top⟩, (by simp;exact fun s =>Eq.symm (eckig_preserves_sSup s))⟩



instance Open.le : LE (Open E) where
  le x y := (x : Sublocale E) ≤ (y : Sublocale E)

def Open.le_iff {U V : Open E} : U ≤ V ↔ U.element ≤ V.element := by
  simp_rw [Open.le, Open.sublocale]
  exact Iff.symm eckig_preserves_inclusion




instance Open.top : Top (Open E) where
  top := ⟨⊤⟩

instance : OrderTop (Open E) where
  le_top a := (by simp[Open.le_iff, Open.top])

@[simp]
lemma Open.top_sublocale : (⊤ : Open E).sublocale = ⊤ := by
  simp [sublocale, Open.top]
  exact eckig_preserves_top

instance Open.bot : Bot (Open E) where
  bot := ⟨⊥⟩

instance : OrderBot (Open E) where
  bot_le a := (by simp[Open.le_iff, Open.bot])

--lemma Open.inf_corresponds {U V : Open X} : U.nucleus ⊓ V.nucleus = eckig (U.element ⊔ V.element) := by
instance Open_sSup: SupSet (Open E) where
  sSup x := ⟨sSup (Open.element '' x)⟩


instance Open_max : Max (Open X) where
  max U V := sSup {U, V}

instance : Min (Open X) where
  min U V := ⟨(U : X) ⊓ V⟩


lemma Open.sSup_eq {U_i : Set (Open X)} : (sSup U_i).sublocale = sSup (Open.sublocale '' U_i) := by
  simp [Open.sublocale, Open_sSup]
  rw [← eckig_preserves_sSup]
  rw [Set.image_image]

lemma Open.Min_eq {U V : Open X} : (U ⊓ V).sublocale = U.sublocale ⊓ V.sublocale := by
  simp [Open.sublocale]
  rw [← eckig_preserves_inf]
  rfl

lemma Open.Max_eq {U V : Open X} : (U ⊔ V).sublocale = U.sublocale ⊔ V.sublocale := by
  let x := @Open.sSup_eq _ _ {U, V}
  simp [Open_max]
  rw [x]
  simp_rw [Sublocale.max_eq]
  rw [Set.image_pair]


lemma open_inf_closed (U V : Open X) : is_open (U.sublocale ⊓ V.sublocale) := by
  rw [is_open]
  use (U ⊓ V)
  rw [eckig_preserves_inf]
  simp [Open.sublocale]


lemma opens_sSup_closed {U_i : Set (Open X)} : is_open (sSup (Open.sublocale '' U_i)) := by
  rw [is_open]
  use (sSup (Open.element '' U_i))
  rw [← eckig_preserves_sSup]
  simp [Open.sublocale]
  rw [Set.image_image]


lemma eckig_injective : Function.Injective (@eckig E e_frm)  := by
  rw [Function.Injective]
  . intro a1 a2 h
    rw [le_antisymm_iff] at h
    rcases h with ⟨h1, h2⟩
    apply le_antisymm
    . exact eckig_preserves_inclusion.mpr h1
    . exact eckig_preserves_inclusion.mpr h2


instance : PartialOrder (Open E) where
  le_refl := (by simp[Open.le])
  le_trans := (by simp[Open.le];exact fun a b c a_1 a_2 =>
    Preorder.le_trans a.sublocale b.sublocale c.sublocale a_1 a_2)
  le_antisymm := (by simp[Open.le,Open.le_iff,Open.ext_iff];intro a b h1 h2; apply le_antisymm;exact h1;exact h2)


lemma Open.sublocale_injective : Function.Injective (@Open.sublocale E e_frm) := by
    rw [Function.Injective]
    simp [Open.sublocale]
    intro a1 a2 h
    rw [le_antisymm_iff] at h
    rcases h with ⟨h1, h2⟩
    ext
    apply le_antisymm
    . exact le_iff.mp h1
    . exact le_iff.mp h2




lemma Open.ext_nucleus (a b : Open E) : a = b ↔ a.sublocale = b.sublocale := by
  simp [Open.sublocale]
  apply Iff.trans Open.ext_iff
  apply Iff.intro
  · intro a_1
    simp_all only
  · intro a_1
    rw [le_antisymm_iff] at *
    apply And.intro
    . apply eckig_preserves_inclusion.mpr a_1.left
    . apply eckig_preserves_inclusion.mpr a_1.right


lemma Open.le_iff_sublocale {a b : Open E} : a ≤ b ↔ a.sublocale ≤ b.sublocale := by
  exact ge_iff_le


lemma Open.le_sup_left : ∀ (a b : Open E), a ≤ a ⊔ b := by
  intro a b
  apply Open.le_iff_sublocale.mpr
  rw [Open.Max_eq]
  exact _root_.le_sup_left

lemma Open.le_sup_right : ∀ (a b : Open E), b ≤ a ⊔ b := by
    intro a b
    apply Open.le_iff_sublocale.mpr
    rw [Open.Max_eq]
    exact _root_.le_sup_right

def Open_to_E (x : Open E) : E := x.element

lemma Open_to_E_injective : Function.Injective (@Open_to_E E e_frm) := by
  rw [Function.Injective]
  simp [Open_to_E]
  exact fun ⦃a₁ a₂⦄ a => Open.ext a

lemma Open_le_sSup : ∀ (s : Set (Open E)), ∀ a ∈ s, a ≤ sSup s := by
  intro s a h
  rw [@Open.le_iff_sublocale]
  rw [@Open.sSup_eq]
  apply le_sSup
  simp only [Set.mem_image]
  use a

lemma Open_sSup_le : ∀ (s : Set (Open E)) (a : Open E), (∀ b ∈ s, b ≤ a) → sSup s ≤ a := by
  intro s a h
  rw [Open.le_iff_sublocale]
  rw [Open.sSup_eq]
  apply sSup_le
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun a a_1 => h a a_1

instance : CompleteSemilatticeSup (Open E) where
  le_sSup := Open_le_sSup
  sSup_le := Open_sSup_le

/-
Leroy Lemme 10
-/




/-
instance : CompleteLattice (Open E) where
  sup x y := x ⊔ y
  le_sup_left := Open.le_sup_left
  le_sup_right := Open.le_sup_right
  sup_le := sorry
  inf x y := x ⊓ y
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry
  le_sSup := sorry
  sSup_le := sorry
  sInf := sorry
  sInf_le :=
-/
