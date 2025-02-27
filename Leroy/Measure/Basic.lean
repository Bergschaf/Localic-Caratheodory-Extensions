import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Further_Topology
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Leroy.Measure.Aux

-----
variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]


def increasingly_filtered {Z : Type*} [PartialOrder Z] (s : Set Z) : Prop :=
  ∀ U ∈ s, ∀ V ∈ s, ∃ W ∈ s, U ≤ W ∧ V ≤ W

def increasing {Z : Type*} [PartialOrder Z] (s : Set Z) : Prop :=
  ∀ U ∈ s, ∃ V ∈ s, U ≤ V

structure Measure where
  toFun : (Open X) → NNReal --
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Open X), U ≤ V → toFun U ≤ toFun V
  pseudosymm (U V : Open X) : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set  (Open X)), increasingly_filtered s → toFun (sSup s) = sSup (toFun '' s)
open Sublocale

variable {m : @Measure E e_frm}

namespace Measure

lemma monotone (u v : Open E) (h : u = v) : m.toFun u = m.toFun v := by
  exact congrArg m.toFun h

@[simp] lemma all_le_top {m : @Measure X h} (a : Open X): m.toFun a ≤ m.toFun ⊤ := m.mono _ _ (OrderTop.le_top a)

noncomputable def caratheodory {m : @Measure X h} (a : Sublocale X) : NNReal :=
  sInf (m.toFun '' Open_Neighbourhood a)

namespace caratheodory


lemma open_eq_toFun {m : @Measure X h} (x : Open X):  m.caratheodory x = m.toFun x := by
  simp [Measure.caratheodory,Open_Neighbourhood]
  apply le_antisymm
  . apply csInf_le'
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use x
  . rw [le_csInf_iff]
    simp
    intro a h
    exact m.mono x a ((Open.le_iff).mpr h)
    exact OrderBot.bddBelow (m.toFun '' {v | x.toSublocale ≤ v.toSublocale})
    simp [Set.Nonempty]
    use m.toFun x
    use x

lemma top_eq_toFun {m : @Measure X h} : m.caratheodory ⊤ = m.toFun ⊤ := by
  simp [caratheodory, Open_Neighbourhood, top_le_iff]
  have h : {v : Open X |  v.toSublocale = ⊤} = {⊤} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    have h1 : (⊤ : Open X).toSublocale = ⊤ := by
      exact Open.top_toSublocale
    rw [← h1]
    exact Iff.symm Open.eq_iff
  rw [h]
  simp only [Set.image_singleton, csInf_singleton]


lemma monotonic {A B : Sublocale E} : A ≤ B → m.caratheodory A ≤ m.caratheodory B := by
  intro h
  simp_rw [Measure.caratheodory]
  apply csInf_le_csInf
  . simp only [BddBelow, Set.Nonempty, lowerBounds, Set.mem_image, forall_exists_index, and_imp,
     forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
    use 0
    intro a ha
    simp only [zero_le]
  . simp [Set.Nonempty, Open_Neighbourhood]
    use m.toFun ⊤
    use ⊤
    simp
  . simp [Open_Neighbourhood, Nucleus.toFun_eq_coe, Set.image_subset_iff]
    rw [@Set.setOf_subset]
    intro x h1
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    use x
    rw [Sublocale.le_iff] at h
    apply And.intro
    . exact fun v => Preorder.le_trans (x.toSublocale v) (B v) (A v) (h1 v) (h v)
    . rfl

lemma le_top (m : Measure) : ∀ a : Sublocale E, m.caratheodory a ≤ m.caratheodory ⊤ := by
  intro a
  apply caratheodory.monotonic
  exact OrderTop.le_top a
end caratheodory
end Measure


lemma Exists_Neighbourhood_epsilon (a : Sublocale E) : ∀ ε > 0,  ∃ w ∈ Open_Neighbourhood a, m.toFun w ≤ m.caratheodory a + ε := by
      have h_aux (ε : Real) (hε : ε > 0) (s : Set Real) (h : s.Nonempty): ∃ W ∈ s, W < sInf s + ε := by
        refine Real.lt_sInf_add_pos ?_ hε
        exact h

      have h_aux' (ε : Real) (hε : ε > 0) (s : Set NNReal) (h : s.Nonempty): ∃ W ∈ s, W < (sInf s) + ε := by
        let h1 := h_aux ε hε (NNReal.toReal '' s) (by simp only [Set.image_nonempty, h])
        simp at h1
        rcases h1 with ⟨x, ⟨h1, h2⟩⟩
        use x
        simp only [h1, true_and]

        apply LT.lt.trans_le h2
        simp only [add_le_add_iff_right]
        rw [← NNReal.coe_sInf]
      rw [Measure.caratheodory]
      have h_nonempty : (m.toFun '' Open_Neighbourhood  a).Nonempty := by
        simp only [Set.Nonempty, Set.mem_image]
        use m.toFun ⊤
        use ⊤
        simp only [and_true]
        exact Open_Neighbourhood.top_mem
      intro ε hε

      let h := h_aux' ε hε (m.toFun '' Open_Neighbourhood a) (by use m.toFun ⊤; rw [Set.mem_image]; use ⊤;simp;exact Open_Neighbourhood.top_mem)
      rcases h with ⟨V, h⟩
      simp at h
      rcases h with ⟨⟨x, ⟨h1, h2⟩⟩, h3⟩
      use x
      simp only [h1, true_and]
      rw [h2]
      exact le_of_lt h3

def ℕpos := {n : ℕ // 0 < n}
def Rpos := {r : NNReal // 0 < r}
/--
Leroy Lemme 1
-> Magie
-/
lemma Measure.caratheodory.preserves_sup (m : @Measure X h) (X_n : ℕ → Sublocale X) (h : increasing (Set.range X_n)) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by
  apply le_antisymm
  .
    have h0 : ∀ ε > 0, m.caratheodory (iSup X_n) ≤ iSup (m.caratheodory ∘ X_n) + ε := by
      intro ε h_ε
      let ε_n (n : ℕ) : ℝ := ε / (2 ^ (n + 1))
      have h_ε_n (n : ℕ) : ε_n n > 0 := by sorry
      have h_sum_1 : 0 < tsum ε_n := by sorry
      have h_sum : tsum ε_n < ε := by
        sorry
      let V_n (n : ℕ) := Classical.choose (@Exists_Neighbourhood_epsilon _ _ m (X_n n) ⟨(ε_n n), sorry⟩ (h_ε_n n))
      have h_V_n (n : ℕ) : m.caratheodory (V_n n) - m.caratheodory (X_n n) < ε_n n := by sorry
      sorry

    have h1 :  ∀ ε > 0, m.caratheodory (iSup X_n) - iSup (m.caratheodory ∘ X_n) ≤  ε := by
      intro e h
      exact tsub_le_iff_left.mpr (h0 e h)

    have h2 :  m.caratheodory (iSup X_n) - iSup (m.caratheodory ∘ X_n) ≤ sInf {ε | ε > 0} := by
      apply le_csInf
      . use 42
        simp
      . exact fun b a => h1 b a
    rw [sInf_epsilon_eq_zero'] at h2
    apply_fun (. + iSup (m.caratheodory ∘ X_n)) at h2
    dsimp at h2
    rw [zero_add] at h2
    apply le_trans' h2
    exact le_tsub_add

  . apply ciSup_le
    intro n
    simp only [Function.comp_apply]
    apply Measure.caratheodory.monotonic
    exact le_iSup X_n n

lemma Measure.caratheodory.subadditive (a b : Sublocale E ) : m.caratheodory (a ⊔ b) ≤ m.caratheodory a + m.caratheodory b := by
  have h : ∀ ε > 0, m.caratheodory (a ⊔ b) ≤ m.caratheodory a + m.caratheodory b + 2 * ε := by
    intro ε h
    have h_a : ∃ w ∈ Open_Neighbourhood a, m.toFun w ≤ m.caratheodory a + ε := by
      exact Exists_Neighbourhood_epsilon a ε h
    have h_b : ∃ w ∈ Open_Neighbourhood b, m.toFun w ≤ m.caratheodory b + ε := by
      exact Exists_Neighbourhood_epsilon b ε h

    rcases h_a with ⟨w_a, ⟨ha1, ha2⟩⟩
    rcases h_b with ⟨w_b, ⟨hb1, hb2⟩⟩
    simp [Open_Neighbourhood] at ha1 hb1
    have h1 : m.caratheodory (a ⊔ b) ≤ m.caratheodory ((w_a ⊔ w_b).toSublocale) := by
      apply Measure.caratheodory.monotonic
      rw [Open.preserves_sup]
      exact sup_le_sup ha1 hb1
    apply le_trans h1
    rw [Measure.caratheodory.open_eq_toFun]
    rw [Measure.pseudosymm]
    simp only [tsub_le_iff_right]
    have h2 : (m.caratheodory a + ε) + (m.caratheodory b +  ε) ≤ m.caratheodory a + m.caratheodory b + 2 * ε + m.toFun (w_a ⊓ w_b) := by
      ring_nf
      simp only [le_add_iff_nonneg_right, zero_le]
    apply le_trans' h2
    apply add_le_add
    exact ha2
    exact hb2

  have h2 :  m.caratheodory (a ⊔ b) - (m.caratheodory a + m.caratheodory b)  ≤ sInf {ε : NNReal | ε > 0} := by
    apply le_csInf
    . simp [Set.Nonempty]
      use 42
      norm_num
    . intro b1 h1
      simp at h1
      let h2 := h (b1 / 2) (by exact half_pos h1)
      apply_fun (fun x : NNReal ↦ (x - (Measure.caratheodory a + Measure.caratheodory b))) at h2
      simp at h2
      have h3 :   m.caratheodory a + m.caratheodory b + 2 * (b1 / 2) - (m.caratheodory a + m.caratheodory b) = b1 := by
        simp only [add_tsub_cancel_left]
        ring_nf
        simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          IsUnit.div_mul_cancel]
      rw [h3] at h2
      apply h2
      --
      simp only [Monotone]
      intro a1 b1 h
      exact tsub_le_tsub_right h (Measure.caratheodory a + Measure.caratheodory b)

  rw [sInf_epsilon_eq_zero'] at h2
  simp at h2
  apply_fun (. + (m.caratheodory a + m.caratheodory b)) at h2
  simp only [zero_add] at h2
  rw [← h2]
  exact le_tsub_add
