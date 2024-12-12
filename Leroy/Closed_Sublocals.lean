import Leroy.Open_Subframes
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

-- complement..

noncomputable def complement (e : Opens E) : Nucleus E where
  toFun x := (open_to_E e) ⊔ x
  idempotent := (by simp)
  increasing := (by simp)
  preserves_inf := (by simp;exact fun x y => sup_inf_left (open_to_E e) x y)






--https://www.mat.uc.pt/preprints/ps/p1639.pdf


--lemma leroy_8 (X: Nucleus E) (X : Opens E): V ⊔ X = ⊤ ↔  (complement V) ≤ X := by


lemma inf_complement (X : Opens E) : X.val ⊓ (complement X) = ⊥ := by
  simp [complement, Nucleus_min, sInf, sSup, e_V_nucleus,Nucleus_bot]



  ext x
  simp [e_V, Nucleus_bot]
  refine sup_eq_top_of_top_mem ?h.h
  simp only [Set.mem_setOf_eq, top_le_iff]
  intro xi h1 h2

  refine (leroy_6a xi x).mp ?h.h.a
  simp
  intro v

  let h2 := h2 v
  rcases h2 with ⟨h3, h4⟩






lemma sup_comp_eq_top (X : Opens E)  : X.val ⊔ (complement X) = ⊤ := by
  simp [complement]
  ext x
  simp [max, sSup, Nucleus_top, e_V_nucleus, e_V]

  apply le_antisymm
  . apply sSup_le
    simp
    intro Y h1 h2
    simp [open_to_E] at h2
    let ch := Classical.choose_spec X.prop
    rw [@Nucleus.ext_iff] at ch
    simp at ch
    let ch_ := ch x


    have h2_ : Y ≤ (Classical.choose X.prop) ⊔ x := by
      exact h2
    --rw [eckig_preserves_inclusion]
    rw [eckig_preserves_inclusion] at h2_
    rw [←ch] at h1
    rw [eckig_preserves_max] at h2_
    rw [@Nucleus.le_iff] at h2_
    simp at h2_
    simp [eckig, e_U] at h1
    have help : x ∈ upperBounds {W | W ⊓ Classical.choose X.prop ≤ x}  := by
      simp [upperBounds]
      intro a h
      sorry

    let h1_ := le_sSup_iff.mp h1 x help
    simp at h1_
    exact h1_







  . apply le_sSup
    simp
    apply And.intro
    . exact Nucleus.increasing' X.val
    . exact SemilatticeSup.le_sup_right (↑(open_to_E X)) x
