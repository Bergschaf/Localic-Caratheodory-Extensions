import Leroy.Open_Subframes
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

-- complement..

noncomputable def complement (e : Nucleus E) (h : is_open e) : Nucleus E where
  toFun x := (open_to_E e h) ⊔ x
  idempotent := (by simp)
  increasing := (by simp)
  preserves_inf := (by simp; exact fun x y => sup_inf_left (↑(open_to_E e h)) x y)


lemma union_comp_eq_top (X : Nucleus E) (h : is_open X) : X ⊔ (complement X h) = ⊤ := by
  simp [complement]
  ext x
  simp [max, sSup, Nucleus_top, e_V_nucleus, e_V]

  apply le_antisymm
  . apply sSup_le
    simp
    intro Y h1 h2
    simp [open_to_E] at h2
    let ch := Classical.choose_spec h
    rw [@Nucleus.ext_iff] at ch
    simp at ch
    let ch_ := ch x


    have h2_ : Y ≤ (Classical.choose h) ⊔ x := by
      exact h2
    sorry




  . apply le_sSup
    simp
    apply And.intro
    . exact Nucleus.increasing' X
    . exact SemilatticeSup.le_sup_right (↑(open_to_E X h)) x


lemma leroy_8 (X V : Nucleus E) (h : is_open V) : V ⊔ X = ⊤ ↔  (complement V h) ≤ X := by
  apply Iff.intro
  sorry
