import Leroy.Open_Subframes
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]


-- TODO define opens and closeds in terms of elements of e, macht alles besser!!!!!!!!


-- complement..

noncomputable def complement (e : Opens E) : Nucleus E where
  toFun x := (open_to_E e) ⊔ x
  idempotent := (by simp)
  increasing := (by simp)
  preserves_inf := (by simp;exact fun x y => sup_inf_left (open_to_E e) x y)



--https://www.mat.uc.pt/preprints/ps/p1639.pdf


--lemma leroy_8 (X: Nucleus E) (X : Opens E): V ⊔ X = ⊤ ↔  (complement V) ≤ X := by


lemma inf_complement (X : Opens E) : X.val ⊓ (complement X) = ⊥ := by
  apply le_antisymm
  . simp only [Nucleus_min, sInf]
    apply sSup_le
    intro b h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_setOf_eq] at h
    rcases h with ⟨h1, h2⟩
    simp [Nucleus_bot]
    intro v
    rw [← Nucleus.idempotent']
    refine eq_top_iff.mpr ?_
    have h : X.val (b v) ≤ b (b v) := by
      simp at h1
      exact h1 (b v)

    have h2 : X.val (complement X v) ≤ X.val (b v) := by
      simp at h2
      simp at h
      let h2 := h2 v
      apply_fun X.val.toFun at h2
      simp at h2
      exact h2
      simp [Nucleus.monotone]

    apply le_trans ?_ h
    apply le_trans ?_ h2
    let u := Classical.choose X.prop
    have hu : open_to_E X = u := by
      exact rfl

    simp [complement]
    rw [hu]
    have hu1 : eckig u = X := by
      exact Set.apply_rangeSplitting eckig X
    rw [← hu1]
    simp [eckig, e_U]
    refine sup_eq_top_of_top_mem ?_
    simp only [Set.mem_setOf_eq, le_top, inf_of_le_right, le_sup_left]

  . simp [Nucleus_bot]


lemma sup_comp_eq_top (X : Opens E)  : X.val ⊔ (complement X) = ⊤ := by
  ext y
  simp [Nucleus_top]

  apply le_antisymm
  .
    apply le_trans (union_pointwise_le y)
    simp [complement]
    rw [@inf_sup_left]
    simp only [sup_le_iff, inf_le_right, and_true]
    let x := Classical.choose X.prop
    let hx := Classical.choose_spec X.prop
    have h : open_to_E X = x := by
      simp [open_to_E]
    rw [h]
    have h1 : eckig x = X := by
      exact hx
    rw [← h1]
    simp [eckig, e_U]
    rw [@sSup_inf_eq]
    simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]

  . exact Nucleus.increasing' (↑X ⊔ complement X)

def is_closed (x : Nucleus X) := ∃ a, complement a = x
def Closeds (X : Type*) [Order.Frame X] := {x : Nucleus X // is_closed x}

lemma sInf_closeds_closed (x : Set (Nucleus X)) (h : ∀ y ∈ x, is_closed y) : is_closed (sInf x) := by sorry

def Nucleus.closure (x : Nucleus X) : Closeds X := ⟨sInf {w : Nucleus X | is_closed w ∧ x ≤ w}, (by sorry)⟩

noncomputable def complement_closeds (x : Closeds X ) : Opens X :=
  Classical.choose x.prop
