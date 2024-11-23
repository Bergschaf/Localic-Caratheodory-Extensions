import Leroy.Nucleus
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice
open CategoryTheory

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]



structure Subframe (X : Type u) [Order.Frame X] where
  e : X ⥤ X
  nucleus : Nucleus e
--  carrier : Set X := Image e

instance : Coe (Subframe X) (Set X) where
  coe x := Image x.e

def subframe_to_subtype (s : Subframe X) : Type u := (s : Set X)



-- Leroy CH 3
instance : LE (Subframe X) where
  le x y := ∀ v : X, y.e.obj v ≤ x.e.obj v


--instance toFrame (U : Subframe X) : Order.Frame (U : Set X) := sorry



def e_V (X_i : Set (Subframe E)) (V : E) := sSup {w : E | ∀ x_i ∈ X_i, w ≤ x_i.e.obj V}

def e_V_monotonic : {X Y : E} → (X ⟶ Y) → (e_V X_i X ⟶ e_V X_i Y) := by
  intro x y h
  simp only [e_V]
  apply homOfLE
  apply sSup_le_sSup
  simp only [Set.setOf_subset_setOf]
  intro a h1 h2 h3
  let h1 := h1 h2 h3
  let h := leOfHom h
  let h4 := h2.e.monotone
  have h5 : h2.e.obj x ≤ h2.e.obj y := by
    exact h4 h
  exact Preorder.le_trans a (h2.e.obj x) (h2.e.obj y) h1 h5

def e_V_functor (X_i : Set (Subframe E)) : E ⥤ E := ⟨⟨e_V X_i, e_V_monotonic⟩, (by aesop_cat), (by aesop_cat)⟩



def e_V_increasing : (x : E) → x ⟶ (e_V_functor X_i).obj x := by
  intro x
  apply homOfLE
  simp [e_V_functor, e_V]
  apply le_sSup
  simp
  intro h h1
  apply (leOfHom (h.nucleus.increasing x))



lemma e_V_idempotent :  ∀ (x : E), (e_V_functor X_i).obj ((e_V_functor X_i).obj x) = (e_V_functor X_i).obj x := by
  intro x
  simp [e_V_functor]

  simp [e_V]
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro x1 h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.e.obj (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x}) ≤ h2.e.obj x := by
      have h7 : (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x}) ≤ h2.e.obj x := by
        simp
        intro b h6
        exact h6 h2 h3
      apply_fun h2.e.obj at h7
      rw [h2.nucleus.idempotent] at h7
      exact h7
      exact h2.e.monotone
    exact
      Preorder.le_trans x1 (h2.e.obj (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x})) (h2.e.obj x)
        (h1 h2 h3) h5
  . apply sSup_le_sSup
    simp
    intro a h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.e.obj x ≤ h2.e.obj (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x}) := by
      have h6 : x ≤ (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x}) := by
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        intro x1 x2
        exact leOfHom (x1.nucleus.increasing x)
      apply_fun h2.e.obj at h6
      exact h6
      exact h2.e.monotone
    exact
      Preorder.le_trans a (h2.e.obj x) (h2.e.obj (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.e.obj x}))
        (h1 h2 h3) h5


lemma e_V_preserves_inf : ∀ (x y : E), (e_V_functor X_i).obj (x ⊓ y) = (e_V_functor X_i).obj x ⊓ (e_V_functor X_i).obj y := by
  intro x y
  simp [e_V_functor]
  have h (W : E) : W ≤ e_V X_i (x ⊓ y)  ↔ W ≤  e_V X_i x ⊓ e_V X_i y := by
    have h1 : W ≤ e_V X_i (x ⊓ y) ↔ ∀ x_i ∈ X_i, W ≤ x_i.e.obj (x ⊓ y) := by
      apply Iff.intro
      . intro h x_i h1
        have h2 : e_V X_i (x ⊓ y) ≤ x_i.e.obj (x ⊓ y) := by
          simp [e_V]
          intro b h2
          exact h2 x_i h1
        exact Preorder.le_trans W (e_V X_i (x ⊓ y)) (x_i.e.obj (x ⊓ y)) h h2
      . intro h
        simp [e_V]
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        exact fun x_i a => h x_i a


    have h2 : (∀ x_i ∈ X_i, W ≤ x_i.e.obj (x ⊓ y)) ↔ ∀ x_i ∈ X_i, W ≤ x_i.e.obj x ⊓ x_i.e.obj y := by
      apply Iff.intro
      . intro h x_i h1
        rw [← x_i.nucleus.preserves_inf]
        exact h x_i h1
      . intro h x_i h1
        rw [x_i.nucleus.preserves_inf]
        exact h x_i h1


    have h3 : (∀ x_i ∈ X_i, W ≤ x_i.e.obj x ⊓ x_i.e.obj y) ↔  W ≤  e_V X_i x ⊓ e_V X_i y := by
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
        let h2 := h2 (x_i.e.obj x)
        let h3 := h3 ((x_i.e.obj y))
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



def e_V_nucleus (X_i : Set (Subframe E)) : Nucleus (e_V_functor X_i) where
  idempotent := e_V_idempotent
  increasing := e_V_increasing
  preserves_inf := e_V_preserves_inf


instance : Order.Frame (Subframe X) := sorry

instance : SupSet (Subframe X) := ⟨fun X_i ↦ ⟨e_V_functor X_i, e_V_nucleus X_i⟩⟩
-- instane : InfSet (Subframe X) ....
