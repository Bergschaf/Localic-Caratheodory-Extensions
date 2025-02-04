import Leroy.Sublocale
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic
variable {E : Type*} [Order.Frame E]

instance : SupSet (Nucleus E) := OrderDual.supSet (Sublocale E)

instance Nucleus.instCompleteLattice : CompleteLattice (Nucleus E) where
  sup x y := sSup {x, y}
  le_sup_left := (by simp )
  le_sup_right := (by simp )
  sup_le := (by simp ;exact fun a b c a_1 a_2 =>
    ⟨a_1, a_2⟩)
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus E)

lemma Nucleus.min_eq (a b : Nucleus E) : a ⊓ b = sInf {a, b} := by rfl

lemma Nucleus.min_eq' (a b : Nucleus E) : ∀ i, (a ⊓ b) i = a i ⊓ b i := by
  intro i
  simp_rw [Nucleus.min_eq, sInf]
  simp [sInf_fun,Set.setOf_or]
  exact inf_comm (b i) (a i)

lemma Nucleus.max_eq (a b : Nucleus E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.max_eq (a b : Sublocale E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.min_eq {a b : Sublocale E} : a ⊓ b = sInf {a, b} := by rfl

lemma Sublocale_le_Nucleus (a : Sublocale E) (b : Nucleus E) : a ≤ b ↔ b ≤ a.nucleus:= by
  rw [@Sublocale.le_iff]
  simp [Sublocale.nucleus]
  exact Iff.symm (Eq.to_iff rfl)

lemma Sublocale.top_eq :∀ x, (⊤ : Sublocale E) x = x := by
  exact fun x => rfl

lemma Sublocale.bot_eq : ∀ x, (⊥ : Sublocale E) x = ⊤ := by
  exact fun x => rfl

@[simp]
lemma Nucleus_mem_sublocale {a : Nucleus E} {s : Set (Sublocale E)} : a ∈ s ↔ a ∈ (Sublocale.nucleus '' s):= by
  exact Iff.symm (Set.mem_image_iff_of_inverse (congrFun rfl) (congrFun rfl))

lemma Nucleus_mem_sublocale' {a : Nucleus E} {s : Set (Sublocale E)} {p : Nucleus E → Prop} : (∀ a ∈ s, p a) ↔ (∀ a ∈ (Sublocale.nucleus '' s), p a) := by
  exact Iff.symm Set.forall_mem_image
lemma Nucleus.le_iff : ∀ a b : Nucleus E, a ≤ b ↔ ∀ i, a i ≤ b i := by exact fun a b => Eq.to_iff rfl

/--
Source Johnstone
-/
def CompleteHeytingAlgebra {α : Type*} [CompleteLattice α] [HeytingAlgebra α] : Order.Frame α := by
  sorry


def himp_toFun (x y : Nucleus E) (a : E) :=
  ⨅ b ≥ a, x b ⇨ y b

/-
Johnstone:
(i): map_inf
(ii): le_apply
(iii): idempotent
-/
def himp_idempotent (x y : Nucleus E) (a : E) :
    himp_toFun x y (himp_toFun x y a) ≤  himp_toFun x y a := by
  have h_0 : ∀ a, ∀ b ≥ a, himp_toFun x y a ≤ x b ⇨ y b := by
    simp [himp_toFun]
    intro a b h
    rw [iInf_inf]
    rw [iInf_le_iff]
    simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
    intro c h1
    rcases h1 b with ⟨h1, h2⟩
    let h1 := h1 h
    apply le_trans' h1
    simp only [le_inf_iff, le_refl, true_and]
    exact h2

  have h : ∀ b ≥ a, (x (x b ⇨ y b)) ⇨ (y (x b ⇨ y b)) = x b ⇨ y b := by
    intro b h
    have h_fixpoint : y (x b ⇨ y b) = x b ⇨ y b := by
      apply le_antisymm
      .
        simp
        rw [himp_eq_sSup]
        have h : y (sSup {w | w ⊓ x b ≤ y b}) ⊓ x b ≤ y (sSup {w | w ⊓ x b ≤ y b}) ⊓ y (x b) := by
          simp
          apply inf_le_of_right_le
          exact Nucleus.le_apply
        apply le_trans h
        rw [← y.map_inf]
        rw [sSup_inf_eq]
        conv =>
          enter [2]
          rw [← y.idempotent]
        apply OrderHomClass.mono
        simp only [Set.mem_setOf_eq, iSup_le_iff]
        exact fun i i => i
      . exact Nucleus.le_apply

    rw [h_fixpoint]
    rw [himp_himp]

    rw [← x.map_inf]
    have h2 : b ≤ x b ⇨ y b := by
      apply le_trans y.le_apply
      simp only [le_himp_iff, inf_le_left]
    rw [inf_of_le_right h2]

  have h1 : himp_toFun x y a = ⨅ b ≥ a, x b ⇨ y b  := by
    simp [himp_toFun]
  conv =>
    enter [2]
    rw [h1]
  conv =>
    enter [2, 1, b, 1]
    intro h1
    rw [← h b h1]
  exact le_iInf₂ fun i j => h_0 (himp_toFun x y a) (x i ⇨ y i) (h_0 a i j)


def himp_le_apply (x y : Nucleus E) (a : E) :
    a ≤ himp_toFun x y a := by
  simp [himp_toFun]
  intro i hi
  refine inf_le_of_left_le ?_
  apply le_trans hi y.le_apply

lemma himp_map_inf (x y : Nucleus E) :
    ∀ (a b : E), himp_toFun x y (a ⊓ b) = himp_toFun x y a ⊓ himp_toFun x y b := by
  intro a b
  apply le_antisymm
  . simp [himp_toFun]
    apply And.intro
    . intro i hi
      rw [iInf_inf]
      rw [iInf_le_iff]
      simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
      intro c h1
      rcases (h1 i) with ⟨h1, h2⟩
      let h1 := h1 (by exact inf_le_of_left_le hi)
      apply le_trans' h1
      rw [inf_of_le_left]
      exact h2
    . intro i hi
      rw [iInf_inf]
      rw [iInf_le_iff]
      simp only [le_inf_iff, le_iInf_iff, le_himp_iff]
      intro c h1
      rcases (h1 i) with ⟨h1, h2⟩
      let h1 := h1 (by exact inf_le_of_right_le hi)
      apply le_trans' h1
      rw [inf_of_le_left]
      exact h2

  . have h : ∀ c ≥ a ⊓ b, c = (a ⊔ c) ⊓ (b ⊔ c) := by
      intro c h
      rw [@inf_sup_left]
      simp only [le_sup_right, inf_of_le_right, right_eq_sup]
      simp at h
      rw [inf_sup_right]
      simp only [sup_le_iff, inf_le_left, and_true]
      exact h
    simp only [himp_toFun]
    conv =>
      enter [2, 1, c, 1]
      intro h1
      rw [h c h1]
      rw [y.map_inf]
      rw [himp_inf_distrib]
      simp

    rw [@le_iInf₂_iff]
    intro i hi
    rw [le_inf_iff]
    apply And.intro
    . apply inf_le_of_left_le
      simp only [ge_iff_le, le_inf_iff]
      . rw [iInf_le_iff]
        have h : x (a ⊔ i) ⇨ y (a ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (a ⊔ i) := by
          simp only [le_himp_iff]
          rw [himp_eq_sSup]
          rw [sSup_inf_eq]
          simp only [Set.mem_setOf_eq, iSup_le_iff]
          intro j h1
          apply le_trans' h1
          simp only [le_inf_iff, inf_le_left, true_and]
          apply inf_le_of_right_le
          exact inf_le_left

        intro c h1
        apply le_trans' h
        simp at h1
        simp
        apply h1
        exact le_sup_left
    . apply inf_le_of_right_le
      simp only [ge_iff_le, le_inf_iff]
      . rw [iInf_le_iff]
        have h : x (b ⊔ i) ⇨ y (b ⊔ i) ≤ (x (a ⊔ i) ⊓ x (b ⊔ i)) ⇨ y (b ⊔ i) := by
          simp only [le_himp_iff]
          rw [himp_eq_sSup]
          rw [sSup_inf_eq]
          simp only [Set.mem_setOf_eq, iSup_le_iff]
          intro j h1
          apply le_trans' h1
          simp only [le_inf_iff, inf_le_left, true_and]
          apply inf_le_of_right_le
          exact inf_le_right

        intro c h1
        apply le_trans' h
        simp at h1
        simp
        apply h1
        exact le_sup_left


def himp_Nucleus (x y : Nucleus E) : Nucleus E where
  toFun := himp_toFun x y
  idempotent' a := himp_idempotent x y a
  le_apply' a := himp_le_apply x y a
  map_inf' a b := himp_map_inf x y a b

instance : HImp (Nucleus E) where
  himp x y := himp_Nucleus x y

lemma le_himp_iff'' : ∀ (a b c : Nucleus E), a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  intro a b c
  simp [himp, himp_Nucleus]
  apply Iff.intro
  . intro h
    simp [Nucleus.le_iff, himp_toFun, Nucleus.min_eq'] at *
    intro i
    apply h i i
    rfl
  . intro h
    simp [Nucleus.le_iff, himp_toFun, Nucleus.min_eq'] at *
    intro i j h1
    have h2 : a i ⊓ b j ≤ a j ⊓ b j := by
      simp
      apply inf_le_of_left_le
      exact OrderHomClass.GCongr.mono a h1
    apply le_trans h2
    apply h


/--
Source: Stone Spaces pp. 51
-/
instance Nucleus.instHeytingAlgebra : HeytingAlgebra (Nucleus E) where
  le_himp_iff := le_himp_iff''
  compl x := x ⇨ ⊥
  himp_bot _ := rfl


--instance (priority := low) : Order.Frame (Nucleus E) := CompleteHeytingAlgebra

-- Temporary until the frame problem gets better
--instance : DistribLattice (Nucleus E) := GeneralizedHeytingAlgebra.toDistribLattice

--instance (priority := high): BoundedOrder (Sublocale E) := by exact OrderDual.instBoundedOrder (Nucleus E)

--instance (priority := high) : OrderTop (Sublocale E) := by exact OrderDual.instOrderTop (Nucleus E)
instance (priority := low) : Order.Coframe (Sublocale E) where
  sdiff := sorry
  sdiff_le_iff := sorry
  hnot := sorry
  top_sdiff := sorry
  iInf_sup_le_sup_sInf := sorry
---

example : ∀ (u : Sublocale E), ⊤ ≤ u ↔ u = ⊤ := fun u => top_le_iff


example (a : Sublocale E) (s : Set (Sublocale E)) :  a ⊔ sInf s = (⨅ b ∈ s, a ⊔ b) := by
  let h1 := @sup_sInf_eq _ _ s a
  apply h1
