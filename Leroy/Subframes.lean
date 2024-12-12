import Leroy.Nucleus
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice
open CategoryTheory

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]



instance le : LE (Nucleus X) where
  le x y := ∀ v : X, y.toFun v ≤ x.toFun v

@[simp]
lemma Nucleus.le_iff {n m : Nucleus X} : n ≤ m ↔ ∀ v : X, m.toFun v ≤ n.toFun v := by rfl

def Nucleus_to_subtype (s : Nucleus X) : Type u := (s : Set X)

-- Leroy CH 3


def e_V (X_i : Set (Nucleus E)) (V : E) := sSup {w : E | ∀ x_i ∈ X_i, w ≤ x_i.toFun V}


def e_V_increasing : (x : E) → x ≤ (e_V X_i) x := by
  intro x
  simp [e_V]
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  exact fun x_i a => x_i.increasing x


lemma e_V_idempotent :  ∀ (x : E), (e_V X_i) (e_V X_i x) = e_V X_i x := by
  intro x
  simp [e_V]
  apply le_antisymm_iff.mpr
  apply And.intro
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
      rw [h2.idempotent] at h7
      exact h7
      exact h2.monotone
    exact
      Preorder.le_trans x1 (h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x})) (h2.toFun x)
        (h1 h2 h3) h5
  . apply sSup_le_sSup
    simp
    intro a h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.toFun x ≤ h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) := by
      have h6 : x ≤ (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) := by
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        intro x1 x2
        exact (x1.increasing x)
      apply_fun h2.toFun at h6
      exact h6
      exact h2.monotone
    exact
      Preorder.le_trans a (h2.toFun x) (h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}))
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



def e_V_nucleus (X_i : Set (Nucleus E)) : Nucleus E where
  toFun := e_V X_i
  idempotent := e_V_idempotent
  increasing := e_V_increasing
  preserves_inf := e_V_preserves_inf


instance : SupSet (Nucleus X) where
  sSup X_i := e_V_nucleus X_i

instance : InfSet (Nucleus X) where
  sInf := fun X_i ↦ sSup {w : Nucleus X | ∀ x_i ∈ X_i, w ≤ x_i}

-- TODO stimmt das??
instance Nucleus_bot : Bot (Nucleus X) where
  bot := ⟨fun x ↦ ⊤, (by simp), (by simp), (by simp)⟩

instance Nucleus_top : Top (Nucleus X) where
  top := ⟨fun x ↦ x, (by simp only [implies_true]), (by simp only [le_refl, implies_true]), (by simp only [implies_true])⟩

lemma all_le_top : ∀ (x : Nucleus X), x ≤ ⊤ := by
  intro x
  simp [Nucleus_top]
  intro v
  exact Nucleus.increasing' x

instance Nucleus_min : Min (Nucleus X) where
  min x y := sInf {x, y}

instance Nucleus_max : Max (Nucleus X) where
  max x y := sSup {x, y}


instance : PartialOrder (Nucleus X) where
  le_refl := (by simp [le])
  le_trans := (by simp [le]; exact fun a b c a_1 a_2 v =>
    Preorder.le_trans (c v) (b v) (a v) (a_2 v) (a_1 v))
  le_antisymm := (by intro a b h i; simp only [le, Nucleus.toFun_eq_coe] at *; ext x; simp only [Nucleus.toFun_eq_coe]; apply le_antisymm; exact i x; exact h x )


--instance bot : Bot (Nucleus E) := sorry
--instance top : Top (Nucleus E) := sorry
--instance : PartialOrder (Nucleus E) := sorry
--instance : SemilatticeSup (Nucleus E) := ⟨sorry,sorry, sorry, sorry⟩
--instance : Lattice (Nucleus E) := ⟨sorry, sorry, sorry, sorry⟩
--instance : CompleteLattice (Nucleus E) := ⟨sorry, sorry, sorry, sorry, sorry, sorry⟩
--instance Nucleus_frame : Order.Frame (Nucleus E) := Order.Frame.ofMinimalAxioms sorry


--  carrier : Set X := Image e

-- TODO subframes als kategorie

-- TODO
--def subframe_embedding (s : Subframe X) : f : FrameHom ... [Embedding ...]

-- def embedding_subframe (f: FrameHom ...) : Subframe ...

-- def subframe_frame


/- Nlab : ein nucleus ist ein quotient frame (-> sublocal)



gamma??:

he double negation sublocale of L, denoted L ¬¬, is given by
j ¬¬(U)≔¬¬U.

This is always a dense subspace; in fact, it is the smallest dense sublocale of L. (As such, even when L is topological, L ¬¬ is rarely topological; in fact, its only points are the isolated points of L.)

--Nuclei -> https://www.sciencedirect.com/science/article/abs/pii/S0022404919301604
-/
