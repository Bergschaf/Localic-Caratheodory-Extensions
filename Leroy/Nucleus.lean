/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Nucleus

namespace Nucleus

variable {X : Type*} [Order.Frame X] (n : Nucleus X)

lemma monotone : Monotone n := n.toClosureOperator.monotone

instance : InfSet (Nucleus X) where
  sInf s :=
  { toFun x := ⨅ f ∈ s, f x,
    map_inf' x y := by
      simp only [InfHomClass.map_inf, le_antisymm_iff, le_inf_iff, le_iInf_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rintro f hf
      · exact iInf₂_le_of_le f hf inf_le_left
      · exact iInf₂_le_of_le f hf inf_le_right
      · exact ⟨inf_le_of_left_le <| iInf₂_le f hf, inf_le_of_right_le <| iInf₂_le f hf⟩
    idempotent' x := iInf₂_mono fun f hf ↦ (f.monotone <| iInf₂_le f hf).trans_eq f.idempotent
    le_apply' x := by simp [le_apply] }

@[simp] theorem sInf_apply (s : Set (Nucleus X)) (x : X) : sInf s x = ⨅ j ∈ s, j x := rfl

@[simp] theorem iInf_apply {ι : Type*} (f : ι → (Nucleus X)) (x : X) : iInf f x = ⨅ j, f j x := by
  rw [iInf, sInf_apply, iInf_range]

instance : CompleteSemilatticeInf (Nucleus X) where
  sInf_le := by simp +contextual [← coe_le_coe, Pi.le_def, iInf_le_iff]
  le_sInf := by simp +contextual [← coe_le_coe, Pi.le_def]

instance : CompleteLattice (Nucleus X) := completeLatticeOfCompleteSemilatticeInf (Nucleus X)

@[simp] theorem inf_aply (m n : Nucleus X) (x : X) : (m ⊓ n) x = m x ⊓ n x := by
  rw [← sInf_pair, sInf_apply, iInf_pair]


instance : HImp (Nucleus X) where
  himp m n :=
  { toFun x := ⨅ y ≥ x, m y ⇨ n y
    idempotent' i := by
      apply le_iInf₂
      intro j hj
      have h : (m (m j ⇨ n j)) ⇨ (n (m j ⇨ n j)) = m j ⇨ n j := by
        have h_fix : n (m j ⇨ n j) = m j ⇨ n j := by
          refine le_antisymm ?_ le_apply
          rw [le_himp_iff, himp_eq_sSup]
          have h1 : n (sSup {w | w ⊓ m j ≤ n j}) ⊓ m j ≤
              n (sSup {w | w ⊓ m j ≤ n j}) ⊓  n (m j) := by
            simp only [le_inf_iff, inf_le_left, true_and]
            exact inf_le_of_right_le le_apply
          apply le_trans h1
          rw [← map_inf, sSup_inf_eq, ← @idempotent _ _ n j]
          gcongr
          apply iSup₂_le
          simp [idempotent]
        rw [h_fix, himp_himp, ← map_inf, inf_of_le_right (le_trans n.le_apply le_himp)]
      rw [← h]
      refine iInf₂_le (m j ⇨ n j) ?_
      simp only [ge_iff_le, le_himp_iff, iInf_inf, iInf_le_iff, le_inf_iff, le_iInf_iff]
      intro b1 h2
      rcases h2 j with ⟨h3, h4⟩
      exact le_trans (by simp[h4]) (h3 (by exact hj))
    map_inf' i j := by
      apply le_antisymm
      · simp only [ge_iff_le, iInf_inf, le_iInf_iff, le_inf_iff, le_himp_iff, iInf_le_iff]
        refine fun k ↦ ⟨fun h1 f h2 ↦ ?_, fun k h1 f h2 ↦ ?_⟩
        all_goals rcases h2 k with ⟨h2_1, h2_2⟩;
        all_goals refine le_trans (inf_of_le_left h2_2).ge (h2_1 ?_)
        · exact inf_le_of_left_le h1
        · exact inf_le_of_right_le h1
      · simp only [ge_iff_le, iInf_inf, le_iInf_iff, le_himp_iff, iInf_le_iff, le_inf_iff]
        intro k h2 l h3
        have h8 : k = (i ⊔ k) ⊓ (j ⊔ k) := by simp [inf_sup_left, inf_sup_right, h2]
        rw [h8, map_inf, le_inf_iff]
        rcases h3 (i ⊔ k) with ⟨⟨h4, h5⟩, h7⟩
        apply And.intro
        · apply le_trans' (h4 le_sup_left)
          simp only [le_inf_iff, le_refl, true_and]
          exact Preorder.le_trans _ _ _ h7 (by gcongr; simp)
        · apply le_trans' (h5 (j ⊔ k) le_sup_left)
          simp only [le_inf_iff, le_refl, true_and]
          exact Preorder.le_trans _ _ _ h7 (by gcongr; simp)
    le_apply' := by
      simp only [ge_iff_le, le_iInf_iff, le_himp_iff]
      refine fun _ _ h ↦ inf_le_of_left_le (le_trans h n.le_apply)}

@[simp] theorem himp_apply (m n : Nucleus X) (x : X) : (m ⇨ n) x = ⨅ y ≥ x, m y ⇨ n y := rfl

instance : HeytingAlgebra (Nucleus X) where
  le_himp_iff _ n _ := by
    simp [← coe_le_coe, Pi.le_def]
    exact ⟨fun h i ↦ h i i le_rfl,
      fun h1 i j _ ↦ le_trans (inf_le_inf_right (n j) (by gcongr)) (h1 j)⟩
  compl m := m ⇨ ⊥
  himp_bot m := rfl

instance : Order.Frame (Nucleus X) where
  __ := instHeytingAlgebra_leroy
  __ := instCompleteLattice_leroy

end Nucleus
