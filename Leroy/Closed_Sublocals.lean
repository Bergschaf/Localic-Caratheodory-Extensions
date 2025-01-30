import Leroy.Open_Sublocales
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]



-- complement..

noncomputable def complement (e : Open E) : Sublocale E where
  toFun x := (e.element) ⊔ x
  idempotent' := (by simp)
  le_apply' := (by simp)
  map_inf' := (by simp;exact fun x y => sup_inf_left e.element x y)


/--
Leroy corollaire after lemme 8
-/
def complement_injective : Function.Injective (@complement E e_frm)  := by
  simp [Function.Injective, complement]
  intro a1 a2 h
  ext
  have h1 : ∀ x, a1.element ⊔ x = a2.element ⊔ x := by
    rw [Nucleus.ext_iff] at h
    simp at h
    exact fun x => h x
  let h2 := h1 ⊥
  simp at h2
  exact h2



lemma inf_complement (X : Open E) : X.toSublocale ⊓ (complement X) = ⊥ := by
  apply le_antisymm
  . simp only [Sublocale.min_eq, sInf]
    apply sSup_le
    intro b h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_setOf_eq] at h
    rcases h with ⟨h1, h2⟩
    simp only [le_bot_iff]
    ext v
    simp only [Nucleus.toFun_eq_coe]
    rw [Sublocale.bot_eq]
    rw [← Nucleus.idempotent]
    refine eq_top_iff.mpr ?_
    have h : X.toSublocale (b v) ≤ b (b v) := by
      simp [Sublocale.le_iff] at h1
      exact h1 (b v)

    have h2 : X.toSublocale (complement X v) ≤ X.toSublocale (b v) := by
      simp [Sublocale.le_iff] at h2
      simp at h
      let h2 := h2 v
      apply_fun X.toSublocale.toFun at h2
      simp at h2
      exact h2
      simp
      exact OrderHomClass.mono X.toNucleus

    apply le_trans ?_ h
    apply le_trans ?_ h2
    simp [complement, Open.toSublocale, eckig, e_U]
    refine sup_eq_top_of_top_mem ?_
    simp [Set.mem_setOf_eq, le_top, inf_of_le_right]
    rw [test]
    exact le_sup_left
  . exact OrderBot.bot_le (X.toSublocale ⊓ complement X)


lemma union_pointwise_le {U V : Sublocale E} :∀ x, (U ⊔ V) x ≤ U x ⊓ V x := by
  intro x
  simp
  simp_rw [Sublocale.max_eq, sSup, sInf]
  rw [← Nucleus.toFun_eq_coe]
  simp [sInf_fun]
  apply And.intro
  . apply sInf_le
    simp only [Set.mem_setOf_eq, true_or]
  . apply sInf_le
    simp only [Set.mem_setOf_eq, or_true]




lemma sup_comp_eq_top (X : Open E)  : X.toSublocale ⊔ (complement X) = ⊤ := by
  ext y
  simp only [Nucleus.toFun_eq_coe]
  rw [Sublocale.top_eq]


  apply le_antisymm
  .
    apply le_trans (union_pointwise_le y)
    simp [complement]
    repeat rw [← Nucleus.toFun_eq_coe]
    simp only [Nucleus.toFun_eq_coe]
    rw [@inf_sup_left]
    simp only [sup_le_iff, inf_le_right, and_true]
    simp only [Open.toSublocale, eckig, e_U]
    rw [@sSup_inf_eq]

    simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]

  . exact Nucleus.le_apply

@[ext]
structure Closed (E : Type*) [Order.Frame E] where
  element : E

protected noncomputable def Closed.toSublocale (c : Closed E) : Sublocale E :=
  complement ⟨c.element⟩


noncomputable instance : Coe (Closed E) (Sublocale E) where
  coe x := x.toSublocale

@[simp]
instance Closed.le : LE (Closed E) where
  le x y := x.toSublocale ≤ y.toSublocale


lemma le_antisymm' :  ∀ (a b : Closed E), a ≤ b → b ≤ a → a = b := by
  intro a b h1 h2
  ext
  simp_all [Closed.toSublocale]
  have h : complement ⟨a.element⟩ = complement ⟨b.element⟩ := by
    ext x
    apply le_antisymm
    . exact h2 x
    . exact h1 x
  apply_fun (fun x ↦ (⟨x⟩ : Open E))
  apply_fun (fun x ↦ complement x)
  simp
  exact h
  exact complement_injective
  simp [Function.Injective]


instance  : PartialOrder (Closed E) where
  le_refl := (by simp)
  le_trans x y z := (by simp[LE.le];exact fun a a_1 v => Preorder.le_trans (z.toSublocale v) (y.toSublocale v) (x.toSublocale v) (a_1 v) (a v))
  le_antisymm  := le_antisymm'

lemma Closed.le_iff (a b : Closed E) : a ≤ b ↔ b.element ≤ a.element := by
  simp [Closed.toSublocale, complement]
  apply Iff.intro
  . intro h
    simp [Sublocale.le_iff] at h
    exact Disjoint.left_le_of_le_sup_right (h ⊥) fun ⦃x⦄ a a => a
  . intro h
    simp only [Sublocale.le_iff, sup_le_iff, le_sup_right, and_true]
    exact fun v => le_sup_of_le_left h


instance Closed.instsInf : InfSet (Closed E) where
  sInf x := ⟨sSup (Closed.element '' x)⟩

instance Closed.instMin : Min (Closed E) where
  min x y := sInf {x, y}


lemma Closed.Min_eq' {x y : Closed E} : x ⊓ y = ⟨x.element ⊔ y.element⟩ := by
  simp [Closed.instMin, Closed.instsInf, Set.image, Set.setOf_or]
  exact sup_comm y.element x.element

lemma Closed.Min_eq {x y : Closed E} : x ⊓ y = x.toSublocale ⊓ y.toSublocale := by
  sorry

lemma Closed_sInf_le : ∀ (s : Set (Closed E)), ∀ a ∈ s, sInf s ≤ a := by
  intro s c hc
  simp [sInf,Closed.toSublocale, complement, LE.le]
  intro i
  refine le_sup_of_le_left ?_
  apply le_sSup
  exact Set.mem_image_of_mem Closed.element hc

lemma Closed_le_sInf : ∀ (s : Set (Closed E)) (a : Closed E), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
  intro s c hc
  simp [sInf, Closed.toSublocale, complement, Sublocale.le_iff]
  simp [Closed.le_iff] at hc
  exact fun x a a_1 => le_sup_of_le_left (hc a a_1)


instance : CompleteSemilatticeInf (Closed E) where
  sInf_le := Closed_sInf_le
  le_sInf := Closed_le_sInf

lemma Open_sSup_corresponds (x : Set E) : sSup x = sSup ((fun x ↦ (⟨x⟩ : Open E)) '' x) := by
  simp [sSup]
  rw [Set.image_image]
  simp only [Set.image_id']


--lemma Nucleus.eq_join_open_closed (n : Nucleus E) : ∃ a b, n = (⟨a⟩ : Open E).toSublocale ⊓ (⟨b⟩ : Closed E).toSublocale := by
--  let k (v : E) := (⟨v⟩ : Open E).toSublocale ⊓ (⟨(n v)⟩ : Closed E).toSublocale
--  sorry

/-
lemma Closed_intersection_corresponds (x : Set (Closed E)) : (sInf x).sublocale = sInf (Closed.sublocale '' x) := by
  simp [sInf, sSup, e_V_nucleus, Closed.sublocale, complement]
  ext y
  simp [e_V]
  apply le_antisymm
  . simp_all only [sup_le_iff, sSup_le_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    apply And.intro
    · intro a a_1
      apply le_sSup
      simp only [Set.mem_setOf_eq]
      intro xi h
      let h := h a a_1 y
      exact h.left
    . apply le_sSup
      simp only [Set.mem_setOf_eq]
      intro xi h
      exact Nucleus.increasing' xi
  · simp only [sSup_le_iff, Set.mem_setOf_eq]
    intro b h
    sorry-/
