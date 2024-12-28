import Leroy.Nucleus
import Mathlib.Order.Synonym

variable {E : Type*} [e_frm : Order.Frame E]

abbrev Sublocale (E : Type*) [Order.Frame E] := (Nucleus E)ᵒᵈ

instance : Coe (Sublocale E) (Nucleus E) where
  coe x := x.ofDual

instance : FunLike (Sublocale E) E E where
  coe x := x.ofDual.toFun
  coe_injective' f g h := (by cases f; cases g; congr)

lemma Sublocale.le_iff (a b : Sublocale E) : a ≤ b ↔ b.ofDual ≤ a.ofDual := (by exact
  ge_iff_le)


--- Leroy SupSet


def e_V (X_i : Set (Sublocale E)) (V : E) := sSup {w : E | ∀ x_i ∈ X_i, w ≤ x_i.toFun V}


def e_V_increasing : (x : E) → x ≤ (e_V X_i) x := by
  intro x
  simp [e_V]
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  exact fun x_i a => x_i.increasing x


lemma e_V_idempotent :  ∀ (x : E), (e_V X_i) (e_V X_i x) ≤ e_V X_i x := by
  intro x
  simp_rw [e_V]
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro x1 h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) ≤ h2.toFun x := by
      have h7 : (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) ≤ h2.toFun x := by
        simp
        intro b h6
        exact h6 h2 h3
      apply_fun h2.toFun at h7
      rw [h2.idempotent'] at h7
      exact h7
      exact h2.monotone
    exact
      Preorder.le_trans x1 (h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x})) (h2.toFun x)
        (h1 h2 h3) h5


lemma e_V_preserves_inf : ∀ (x y : E), (e_V X_i) (x ⊓ y) = (e_V X_i) x ⊓ e_V X_i y := by
  intro x y
  have h (W : E) : W ≤ e_V X_i (x ⊓ y)  ↔ W ≤  e_V X_i x ⊓ e_V X_i y := by
    have h1 : W ≤ e_V X_i (x ⊓ y) ↔ ∀ x_i ∈ X_i, W ≤ x_i.toFun (x ⊓ y) := by
      apply Iff.intro
      . intro h x_i h1
        have h2 : e_V X_i (x ⊓ y) ≤ x_i.toFun (x ⊓ y) := by
          simp [e_V]
          intro b h2
          exact h2 x_i h1
        exact Preorder.le_trans W (e_V X_i (x ⊓ y)) (x_i.toFun (x ⊓ y)) h h2
      . intro h
        simp [e_V]
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        exact fun x_i a => h x_i a


    have h2 : (∀ x_i ∈ X_i, W ≤ x_i.toFun (x ⊓ y)) ↔ ∀ x_i ∈ X_i, W ≤ x_i.toFun x ⊓ x_i.toFun y := by
      apply Iff.intro
      . intro h x_i h1
        rw [← x_i.preserves_inf]
        exact h x_i h1
      . intro h x_i h1
        rw [x_i.preserves_inf]
        exact h x_i h1


    have h3 : (∀ x_i ∈ X_i, W ≤ x_i.toFun x ⊓ x_i.toFun y) ↔  W ≤  e_V X_i x ⊓ e_V X_i y := by
      apply Iff.intro
      . intro h
        simp [e_V]
        simp at h
        apply And.intro
        . apply le_sSup
          simp
          intro x_i h1
          let h := h x_i h1
          apply h.left
        . apply le_sSup
          simp
          intro x_i h1
          let h := h x_i h1
          apply h.right
      . intro h x_i h1
        simp only [le_inf_iff]
        simp [e_V] at h
        rcases h with ⟨h2, h3⟩
        simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq] at h2 h3
        let h2 := h2 (x_i.toFun x)
        let h3 := h3 ((x_i.toFun y))
        apply And.intro
        . apply h2
          intro a h3
          exact h3 x_i h1
        . apply h3
          intro a h3
          exact h3 x_i h1

    apply Iff.trans h1
    apply Iff.trans h2 h3

  apply le_antisymm_iff.mpr

  apply And.intro
  . have h1 := h (e_V X_i (x ⊓ y))
    rcases h1 with ⟨h1, h2⟩
    apply (h1 (by rfl))
  . have h1 := h (e_V X_i x ⊓ e_V X_i y )
    rcases h1 with ⟨h1, h2⟩
    apply (h2 (by rfl))


def e_V_sublocale (X_i : Set (Sublocale E)) : Sublocale E where
  toFun := e_V X_i
  idempotent := e_V_idempotent
  increasing := e_V_increasing
  preserves_inf := e_V_preserves_inf

lemma le_e_V : ∀ (s : Set (Sublocale E)), ∀ a ∈ s, a ≤ e_V_sublocale s := by
  intro s a ha
  simp [e_V_sublocale]
  apply Nucleus.le_iff.mpr
  intro v
  simp [e_V]
  exact fun b a_1 => a_1 a ha

lemma e_V_le : ∀ (s : Set (Sublocale E)), ∀ (a : (Sublocale E)), (∀ b ∈ s, b ≤ a) → e_V_sublocale s ≤ a := by
  intro s a h
  simp [e_V_sublocale]
  apply Nucleus.le_iff.mpr
  intro v
  simp [e_V]
  apply le_sSup_iff.mpr
  simp [upperBounds]
  intro b h1
  apply h1
  intro ai hai
  exact h (OrderDual.toDual ai) hai v


theorem leroy_eq_stone (s : Set (Sublocale E)) : e_V_sublocale s = sSup s := by
  have h1 : e_V_sublocale s ∈ upperBounds s := by
    simp [upperBounds]
    intro a h
    apply le_e_V
    exact h

  have h2 : sSup s ∈ upperBounds s := by
    simp [upperBounds]
    intro a h
    apply le_sSup
    exact h

  have h3 : ∀ x ∈ upperBounds s, sSup s ≤ x := by
    exact fun x a => CompleteSemilatticeSup.sSup_le s x a

  have h4 : ∀ x ∈ upperBounds s, e_V_sublocale s ≤ x := by
    exact fun x a => e_V_le s x a

  apply le_antisymm
  . exact h4 (sSup s) h2
  . exact h3 (e_V_sublocale s) h1

instance : InfSet (Sublocale E) where
  sInf X_i := sSup {w | ∀ x ∈ X_i, w ≤ x}

lemma Sublocale_sInf_le : ∀ (s : Set (Sublocale E)), ∀ a ∈ s, sInf s ≤ a := by
  simp [sInf]
  intro s a h a1 h1
  exact h1 a h

lemma Sublocale_le_sInf : ∀ (s : Set (Sublocale E)) (a : Sublocale E), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
  intro s a h
  simp [sInf]
  apply le_sSup_iff.mpr
  simp only [upperBounds, Set.mem_setOf_eq, OrderDual.forall, OrderDual.toDual_le_toDual]
  intro a1 h1
  apply h1
  exact fun a a_1 => h a a_1

instance : CompleteSemilatticeInf (Sublocale E) where
  sInf_le := Sublocale_sInf_le
  le_sInf := Sublocale_le_sInf
