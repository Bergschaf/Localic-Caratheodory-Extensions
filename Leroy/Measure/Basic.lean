module

public import Leroy.Measure.Preliminaries
public import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Measures on frames and the Caratheodory extension

This file introduces the notion of a measure on the frame of open sublocales of a
topological space, develops the strictly additive calculus of such measures, and
studies the Caratheodory extension of a measure from opens to arbitrary sublocales,
in particular its preservation of increasing suprema and its subadditivity, as used
in the localic Caratheodory extension theorem.
-/

@[expose] public section

variable {X Y E ι : Type*} [h : Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]
  [PartialOrder ι] [Nonempty ι]

/-- A set `s` in a partially ordered space is increasingly filtered if any two of its
elements admit a common upper bound that again lies in `s`. -/
def increasingly_filtered {Z : Type*} [PartialOrder Z] (s : Set Z) : Prop :=
  ∀ U ∈ s, ∀ V ∈ s, ∃ W ∈ s, U ≤ W ∧ V ≤ W

/-- A family of sublocales `V : ι → Sublocale E` indexed by a nonempty partial order
`ι` is decreasingly filtered if any two of its members admit a common lower bound in
the family. -/
def decreasingly_filtered (V : ι → Sublocale E) : Prop :=
  ∀ n m : ι, ∃ l, V l ≤ V n ∧ V l ≤ V m

/-- A measure on the frame `Open X` of open sublocales of `X` is a function to `NNReal`
which vanishes on the empty open, is monotone, is strictly additive
(inclusion-exclusion on binary suprema) and extends to suprema of increasingly
filtered sets of opens. -/
structure Measure where
  toFun : (Open X) → NNReal
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Open X), U ≤ V → toFun U ≤ toFun V
  strictly_additive (U V : Open X) : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set  (Open X)), increasingly_filtered s → toFun (sSup s) = sSup (toFun '' s)

open Sublocale

variable {m : @Measure E e_frm}

namespace Measure

/-- The strict additivity property of `m` rearranged into the inclusion-exclusion
identity `m U + m V = m (U ⊓ V) + m (U ⊔ V)`. -/
lemma strictly_additive'' (U V : Open E) :
    m.toFun U + m.toFun V = m.toFun (U ⊓ V) + m.toFun (U ⊔ V) := by
  have h_inf : m.toFun (U ⊓ V) ≤ m.toFun U + m.toFun V :=
    (m.mono _ _ inf_le_left).trans (le_add_of_nonneg_right zero_le)
  rw [m.strictly_additive]
  exact (tsub_add_cancel_of_le h_inf).symm.trans (add_comm _ _)

/-- The strict additivity of `m` in subtractive form: the measure of the intersection
is obtained from the measures of `U` and `V` by subtracting the measure of their
supremum. -/
lemma strictly_additive' (U V : Open E) :
    m.toFun (U ⊓ V) = m.toFun U + m.toFun V - m.toFun (U ⊔ V) := by
  have h_inf : m.toFun (U ⊓ V) ≤ m.toFun U + m.toFun V :=
    (m.mono _ _ inf_le_left).trans (le_add_of_nonneg_right zero_le)
  rw [m.strictly_additive]
  exact (tsub_tsub_cancel_of_le h_inf).symm

/-- For an increasingly filtered family of opens `f`, the measure of the supremum of
the family is the supremum of the measures along `f`. -/
lemma iSup_filtered {ι : Type*} :
    ∀ (f : ι → Open E), increasingly_filtered (Set.range f) →
      m.toFun (iSup f) = iSup (m.toFun ∘ f) := by
  intro f h
  repeat rw [iSup]
  rw [m.filtered (Set.range f) h]
  rw [Set.range_comp]

/-- `m.toFun` respects propositional equality of opens; a trivial reformulation of
congruence. -/
lemma toFun_congr (u v : Open E) (h : u = v) : m.toFun u = m.toFun v := by
  exact congrArg m.toFun h

/-- Every open has measure bounded by the measure of the top open. -/
@[simp] lemma all_le_top {m : @Measure X h} (a : Open X) :
    m.toFun a ≤ m.toFun ⊤ := m.mono _ _ (OrderTop.le_top a)

/-- The Caratheodory outer measure of a sublocale `a`: the infimum of the measures of
the open neighbourhoods of `a`. -/
noncomputable def caratheodory {m : @Measure X h} (a : Sublocale X) : NNReal :=
  sInf (m.toFun '' openNhds a)

namespace caratheodory

/-- On an open sublocale the Caratheodory measure agrees with the original measure
`m`; this says the extension does not change values on opens. -/
lemma open_eq_toFun {m : @Measure X h} (x : Open X) :
    m.caratheodory x = m.toFun x := by
  simp only [caratheodory, openNhds]
  apply le_antisymm
  · apply csInf_le'
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    use x
  · rw [le_csInf_iff]
    · simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro a h
      exact m.mono x a ((Open.le_iff).mpr h)
    · exact OrderBot.bddBelow (m.toFun '' {v | x.toSublocale ≤ v.toSublocale})
    · simp only [Set.image_nonempty]
      exact ⟨x, le_refl x.toSublocale⟩

/-- The Caratheodory measure of the top sublocale equals the measure of the top open. -/
lemma top_eq_toFun {m : @Measure X h} : m.caratheodory ⊤ = m.toFun ⊤ := by
  simp only [Measure.caratheodory, openNhds, top_le_iff]
  have h : {v : Open X |  v.toSublocale = ⊤} = {⊤} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    have h1 : (⊤ : Open X).toSublocale = ⊤ := by
      exact Open.top_toSublocale
    rw [← h1]
    exact Iff.symm Open.eq_iff
  rw [h]
  simp only [Set.image_singleton, csInf_singleton]

/-- The Caratheodory measure is monotone: `A ≤ B` implies the Caratheodory measure of
`A` is at most that of `B`. -/
lemma mono {A B : Sublocale E} : A ≤ B → m.caratheodory A ≤ m.caratheodory B := by
  intro h
  simp_rw [Measure.caratheodory]
  apply csInf_le_csInf
  · simp only [BddBelow, Set.Nonempty, lowerBounds, Set.mem_image, forall_exists_index, and_imp,
     forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq]
    use 0
    intro a ha
    simp only [zero_le]
  · simp only [Set.Nonempty, openNhds, Set.mem_image, Set.mem_ofPred_eq, ↓existsAndEq,
    and_true]
    use ⊤
    simp
  · simp only [openNhds, Set.image_subset_iff]
    rw [@Set.ofPred_subset]
    intro x h1
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    use x
    apply And.intro
    · exact le_trans h h1
    · rfl

/-- The Caratheodory measure of any sublocale is at most its value at the top, since
the Caratheodory measure is monotone. -/
lemma le_top (m : Measure) : ∀ a : Sublocale E, m.caratheodory a ≤ m.caratheodory ⊤ := by
  intro a
  apply caratheodory.mono
  exact OrderTop.le_top a

/-- The Caratheodory measure of any sublocale is at most the measure of the top open. -/
lemma le_top_toFun (m : Measure) : ∀ a : Sublocale E, m.caratheodory a ≤ m.toFun ⊤ := by
  intro a
  rw [← top_eq_toFun]
  exact le_top m a

/-- The Caratheodory measure of the bottom sublocale vanishes, since the bottom open
is an open neighbourhood of `⊥` and has measure zero. -/
lemma bot_eq_0 (m : @Measure E _) : m.caratheodory ⊥ = 0 := by
  rw [← Open.bot_toSublocale, open_eq_toFun, empty]

end caratheodory
end Measure

/-- Auxiliary lemma for Leroy's Lemme 1: for every `ε > 0` the sublocale `a` admits an
open neighbourhood whose measure is at most `m.caratheodory a + ε`, i.e. the infimum in
the definition of the Carathéodory measure is attained up to `ε`. -/
lemma Measure.exists_mem_openNhds_le (a : Sublocale E) :
  ∀ ε > 0,  ∃ w ∈ openNhds a, m.toFun w ≤ m.caratheodory a + ε := by
    have h_aux (ε : Real) (hε : ε > 0) (s : Set Real) (h : s.Nonempty) :
        ∃ W ∈ s, W < sInf s + ε := by
      refine Real.lt_sInf_add_pos ?_ hε
      exact h
    have h_aux' (ε : Real) (hε : ε > 0) (s : Set NNReal) (h : s.Nonempty) :
        ∃ W ∈ s, W < (sInf s) + ε := by
      let h1 := h_aux ε hε (NNReal.toReal '' s) (by simp only [Set.image_nonempty, h])
      simp only [Set.mem_image, exists_exists_and_eq_and] at h1
      rcases h1 with ⟨x, ⟨h1, h2⟩⟩
      use x
      simp only [h1, true_and]
      apply LT.lt.trans_le h2
      simp only [add_le_add_iff_right]
      rw [← NNReal.coe_sInf]
    rw [Measure.caratheodory]
    have h_nonempty : (m.toFun '' openNhds  a).Nonempty := by
      simp only [Set.Nonempty, Set.mem_image]
      use m.toFun ⊤
      use ⊤
      simp only [and_true]
      exact openNhds_top_mem
    intro ε hε
    let h := h_aux' ε hε (m.toFun '' openNhds a) h_nonempty
    rcases h with ⟨V, h⟩
    simp only [Set.mem_image] at h
    rcases h with ⟨⟨x, ⟨h1, h2⟩⟩, h3⟩
    use x
    simp only [h1, true_and]
    rw [h2]
    exact le_of_lt h3

/-- Auxiliary lemma, sharper form of `Measure.exists_mem_openNhds_le` with a strict
inequality: for every `ε > 0` there is an open neighbourhood of `a` whose measure is
strictly smaller than `m.caratheodory a + ε`. -/
lemma Measure.exists_mem_openNhds_lt (a : Sublocale E) :
    ∀ ε > 0,  ∃ w ∈ openNhds a, m.toFun w < m.caratheodory a + ε := by
  intro ε h_ε
  obtain ⟨w, ⟨h1, h2⟩⟩ := @Measure.exists_mem_openNhds_le _ _ m a (ε / 2) (by exact half_pos h_ε)
  use w
  use h1
  apply LE.le.trans_lt h2
  simp only [add_lt_add_iff_left, half_lt_self_iff]
  exact h_ε

/-- **Leroy, Lemme 1** (Ch. IV): for an increasing sequence of sublocales, the
Carathéodory measure of the supremum is the supremum of the measures,
`μ(⋃ Xn) = sup μ(Xn)`. -/
lemma Measure.caratheodory.preserves_sup' (m : @Measure X h) (X_n : ℕ → Sublocale X)
    (h : Monotone X_n) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by
  apply le_antisymm
  · have h0 : ∀ ε > 0, m.caratheodory (iSup X_n) ≤ iSup (m.caratheodory ∘ X_n) + ε := by
      intro ε h_ε
      let ε_n (n : ℕ) : ℝ := ε / (2 ^ (n + 1))
      have h_ε_n (n : ℕ) : ε_n n > 0 := by
        simp [ε_n, h_ε]
      have h_sum (n : ℕ) : ∑ m ∈ Finset.range (n), ε_n m ≤ ε := by
        -- TODO: the geometric-series estimate might be available in Mathlib
        have h_geometric_sum (n : ℕ) :
            ∑ m ∈ Finset.range (n), ε_n m = ε - ε * 2 ^ (- ↑(n : ℤ)) := by
          induction n with
          | zero => simp
          | succ n ih =>
            rw [Finset.sum_range_succ]
            rw [ih]
            simp only [zpow_neg, zpow_natCast, Nat.cast_add, Nat.cast_one, neg_add_rev,
              Int.reduceNeg]
            have h_left :
                ↑ε - ↑ε * (2 ^ n)⁻¹ + ↑ε / 2 ^ (n + 1) = ε.val - ε / (2 ^ (n + 1)) := by
              have h1 : ↑ε.toReal * (2 ^ n)⁻¹ = ↑ε.toReal / 2 ^ n := by
                exact rfl
              rw [h1]
              rw [sub_add_eq_add_sub]
              rw [add_sub_assoc]
              have h2 :
                  ↑ε.toReal / 2 ^ (n + 1) - ↑ε.toReal / 2 ^ n =
                    ↑ε.toReal / 2 ^ n * (1 / 2 - 1) := by
                rw [mul_sub]
                ring
              rw [h2]
              have h3 : ((1 / 2 - 1) : ℝ) = (-1 / 2) := by ring
              rw [h3]
              rw [mul_div]
              simp only [mul_neg, mul_one, NNReal.val_eq_coe]
              ring
            rw [h_left]
            have h_right :
                ↑ε - ↑ε * 2 ^ (-1 + -↑(n : ℤ)) = ε.val - ε / (2 ^ (n + 1)) := by
              have h4 : ↑ε.toReal * 2 ^ (-1 + -↑(n : ℤ)) = ↑ε.toReal / 2 ^ (n + 1) := by
                have h5 : (-(1 : ℤ) + -↑(n : ℤ)) = -(((n + 1) : ℕ) : ℤ) := by
                  simp only [Int.reduceNeg, Nat.cast_add, Nat.cast_one, neg_add_rev]
                rw [h5]
                have h6 (a b : ℝ) (n : ℕ) : a * b ^ (-(n : ℤ)) = a / b ^ n := by
                  simp only [zpow_neg, zpow_natCast]
                  rfl
                rw [h6]
              rw [h4]
              rfl
            rw [h_right]
        rw [h_geometric_sum]
        simp
      let V_n (n : ℕ) :=
        Classical.choose (@Measure.exists_mem_openNhds_lt _ _ m (X_n n) ⟨(ε_n n),
          (by exact le_of_lt (h_ε_n n))⟩ (h_ε_n n))
      have h_V_n (n : ℕ) :
          m.caratheodory (V_n n) - m.caratheodory (X_n n) < ε_n n := by
        obtain ⟨h1, h2⟩ := Classical.choose_spec
          (@Measure.exists_mem_openNhds_lt _ _ m (X_n n) ⟨(ε_n n),
            (by exact le_of_lt (h_ε_n n))⟩ (h_ε_n n))
        simp only [V_n]
        rw [Measure.caratheodory.open_eq_toFun]
        apply_fun NNReal.toReal at h2
        · simp only [NNReal.coe_lt_coe] at h2
          exact sub_left_lt_of_lt_add h2
        · exact fun ⦃a b⦄ a => a
      have h_V_n' (n : ℕ) :
          m.caratheodory (V_n n) < m.caratheodory (X_n n) + ε_n n := by
        exact lt_add_of_tsub_lt_left (h_V_n n)
      have X_n_le_V_n (n : ℕ) : X_n n ≤ V_n n := by
        obtain ⟨h1, h2⟩ := Classical.choose_spec
          (@Measure.exists_mem_openNhds_lt _ _ m (X_n n) ⟨(ε_n n),
            (by exact le_of_lt (h_ε_n n))⟩ (h_ε_n n))
        simp only [V_n]
        simp only [openNhds, Set.mem_ofPred_eq] at h1
        exact h1
      let W_n (n : ℕ) := ⨆ m ∈ {i : ℕ | i ≤ n}, V_n m
      have V_n_le_W_n (n : ℕ) : V_n n ≤ W_n n := by
        simp only [Set.mem_ofPred_eq, le_iSup_iff, iSup_le_iff, W_n]
        intro b h
        exact h n (by rfl)
      let W := iSup W_n
      have h1 (n : ℕ) :
          m.caratheodory (W_n n) - m.caratheodory (X_n n) ≤
            ∑ m ∈ Finset.range (n+1), ε_n m := by
        induction n with
        | zero =>
          simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero, iSup_iSup_eq_left, zero_add,
            Finset.range_one, Finset.sum_singleton, W_n]
          exact le_of_lt (h_V_n 0)
        | succ n ih =>
          have h2 : m.caratheodory (W_n (n + 1)) ≤
              m.caratheodory (W_n n) - m.caratheodory (X_n n) +
                m.caratheodory (X_n (n + 1)) + ε_n (n + 1) := by
            have h_w_n : (W_n (n + 1)) = W_n n ⊔ V_n (n + 1) := by
              simp only [Set.mem_ofPred_eq, W_n]
              have h_help :
                  (⨆ m, ⨆ (_ : m ≤ n), V_n m) ⊔ V_n (n + 1) =
                    ⨆ m, ⨆ (_ : m ≤ n), V_n m ⊔ V_n (n + 1) := by
                refine biSup_sup ?_
                use 0
                exact Nat.zero_le n
              apply le_antisymm
              · rw [h_help]
                simp only [iSup_le_iff]
                intro i h
                simp only [le_iSup_iff, iSup_le_iff, sup_le_iff]
                rintro b h1
                by_cases hC : i ≤ n
                · obtain ⟨h2, _⟩ := h1 i hC
                  exact h2
                · have h_help : i = n + 1 := by
                    simp only [not_le] at hC
                    exact Nat.le_antisymm h hC
                  rw [h_help]
                  obtain ⟨_ , h2⟩ := h1 0 (by exact Nat.zero_le n)
                  exact h2
              · rw [h_help]
                simp only [iSup_le_iff, sup_le_iff]
                intro i h
                apply And.intro
                · simp only [le_iSup_iff, iSup_le_iff]
                  intro b h1
                  exact h1 i (by exact Nat.le_add_right_of_le h)
                · simp only [le_iSup_iff, iSup_le_iff]
                  intro b h1
                  exact h1 (n + 1) (by exact Nat.le_refl (n + 1))
            rw [h_w_n, Measure.caratheodory.open_eq_toFun]
            rw [Measure.strictly_additive]
            have h2 : ↑((m.toFun (W_n n) + m.toFun (V_n (n + 1)) - m.toFun (W_n n ⊓ V_n (n + 1)))) ≤
                ↑(m.toFun (W_n n) + m.toFun (V_n (n + 1)) - m.caratheodory (X_n n)) := by
              apply tsub_le_tsub
              · rfl
              · rw [← Measure.caratheodory.open_eq_toFun]
                apply Measure.caratheodory.mono
                rw [Open.preserves_inf]
                apply le_inf
                · let h2 := V_n_le_W_n n
                  rw [Open.le_iff] at h2
                  apply le_trans' h2 (X_n_le_V_n n)
                · apply le_trans (h (show n ≤ n + 1 by norm_num)) -- Hier wird Monotone benutzt
                  exact X_n_le_V_n (n + 1)
            apply_fun NNReal.toReal at h2
            · apply le_trans h2
              rw [Measure.caratheodory.open_eq_toFun]
              rw [NNReal.coe_sub]
              · rw [NNReal.coe_add]
                repeat rw [sub_eq_add_neg]
                conv =>
                  enter [1]
                  rw [add_assoc]
                rw [add_assoc]
                rw [add_assoc]
                apply add_le_add
                · rfl
                · rw [add_comm]
                  apply add_le_add
                  · rfl
                  · rw [← Measure.caratheodory.open_eq_toFun]
                    exact le_of_lt (h_V_n' (n + 1))
              · rw [← Measure.caratheodory.open_eq_toFun (W_n n)]
                have hXW : X_n n ≤ (W_n n).toSublocale :=
                  (X_n_le_V_n n).trans (Open.le_iff.mp (V_n_le_W_n n))
                exact le_trans (Measure.caratheodory.mono (A := X_n n) (B := W_n n) hXW)
                  (le_add_of_nonneg_right zero_le)
            · exact fun ⦃a b⦄ a => a
          have h3 : m.caratheodory (W_n (n + 1)) - m.caratheodory (X_n (n + 1)) ≤
              m.caratheodory (W_n n) - m.caratheodory (X_n n) + ε_n (n + 1) := by
            simp only [tsub_le_iff_right]
            apply le_trans h2
            linarith
          have h4 : m.caratheodory (W_n (n + 1)) - m.caratheodory (X_n (n + 1)) ≤
              (∑ m ∈ Finset.range (n+1), ε_n ↑m) + ε_n (n + 1) := by
            apply le_trans h3
            simp only [add_le_add_iff_right]
            exact ih
          have h5 : (∑ m ∈ Finset.range (n+1), ε_n ↑m) + ε_n (n + 1) ≤
              ∑ m ∈ Finset.range (n+2), ε_n ↑m := by
            rw [← Finset.sum_range_succ]
          apply le_trans h4 h5
      have h2 (n : ℕ) :
          m.caratheodory (W_n n) ≤ m.caratheodory (X_n n) +
            ∑ m ∈ Finset.range (n+1), ε_n m := by
        exact tsub_le_iff_left.mp (h1 n)
      have h3 : iSup (fun n ↦ m.caratheodory (W_n n)) ≤
          iSup (fun n ↦ m.caratheodory (X_n n) + ∑ m ∈ Finset.range (n+1), ε_n m) := by
        simp only [NNReal.coe_iSup]
        apply ciSup_le
        intro n
        apply le_trans (h2 n)
        refine le_ciSup_of_le ?_ n ?_
        · simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_range, forall_exists_index,
            forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
          use m.caratheodory ⊤ + ε
          intro a
          apply add_le_add
          · norm_cast
            exact le_top m (X_n a)
          · exact h_sum (a + 1)
        · rfl
      clear h3
      have h4 : m.caratheodory (iSup X_n) ≤ ⨆ i : ℕ, ↑(m.caratheodory (W_n i).toSublocale) := by
        conv =>
          enter [2, 1, i]
          rw [Measure.caratheodory.open_eq_toFun]
        have h_filtered : increasingly_filtered (Set.range W_n) := by
          simp only [increasingly_filtered, Set.mem_range, exists_exists_eq_and,
            forall_exists_index, forall_apply_eq_imp_iff]
          intro i j
          use i + j
          have h_mono : Monotone W_n := by
            simp only [Monotone, Set.mem_ofPred_eq, le_iSup_iff, iSup_le_iff, W_n, V_n, ε_n]
            intro n b h m h2 i hn
            apply h2 i (le_trans hn h)
          refine ⟨?_, ?_⟩ <;> exact h_mono (by norm_num)
        let h := m.iSup_filtered W_n h_filtered
        rw [Function.comp_def] at h
        rw [← h]
        rw [← Measure.caratheodory.open_eq_toFun]
        apply Measure.caratheodory.mono
        simp only [Open.preserves_iSup, le_iSup_iff, iSup_le_iff]
        intro a h i
        apply le_trans' (h i)
        let h1 := (V_n_le_W_n i)
        rw [Open.le_iff] at h1
        apply le_trans' h1
        exact X_n_le_V_n i
      apply le_trans h4
      refine (ciSup_le_iff ?_).mpr ?_
      · use m.caratheodory ⊤
        simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
          Set.mem_ofPred_eq]
        exact fun a => le_top m (W_n a).toSublocale
      · intro i
        have h_help : iSup (m.caratheodory ∘ X_n)  = ⨆ i : ℕ, m.caratheodory (X_n i) := by
          rfl
        have h_help' : (⨆ i : ℕ, m.caratheodory (X_n i)) + ε =
            ⨆ i : ℕ, m.caratheodory (X_n i) + ε := by
          apply_fun NNReal.toReal
          · simp only [NNReal.coe_add, NNReal.coe_iSup]
            rw [ciSup_add]
            use m.caratheodory ⊤
            simp only [upperBounds, Set.mem_range, forall_exists_index,
              forall_apply_eq_imp_iff]
            exact fun a => le_top m (X_n a)
          · exact NNReal.coe_injective
        rw [h_help, h_help']
        rw [le_ciSup_iff']
        · intro b h
          apply le_trans' (h i)
          apply le_trans (h2 i)
          simp only [NNReal.val_eq_coe, NNReal.coe_add, add_le_add_iff_left]
          exact h_sum (i + 1)
        · use m.caratheodory ⊤ + ε
          simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
            Set.mem_ofPred_eq, add_le_add_iff_right]
          exact fun a => le_top m (X_n a)
    have h1 :  ∀ ε > 0, m.caratheodory (iSup X_n) - iSup (m.caratheodory ∘ X_n) ≤  ε := by
      intro e h
      exact tsub_le_iff_left.mpr (h0 e h)
    have h2 :  m.caratheodory (iSup X_n) - iSup (m.caratheodory ∘ X_n) ≤ sInf {ε | ε > 0} := by
      apply le_csInf
      · use 42
        simp
      · exact fun b a => h1 b a
    rw [sInf_epsilon_eq_zero'] at h2
    exact (tsub_le_iff_right.mp h2).trans (zero_add _).le
  · apply ciSup_le
    intro n
    simp only [Function.comp_apply]
    apply Measure.caratheodory.mono
    exact le_iSup X_n n

/-- Subadditivity of the Caratheodory measure: the Caratheodory measure of a supremum
`a ⊔ b` is at most the sum of the Caratheodory measures of `a` and `b`. -/
lemma Measure.caratheodory.subadditive (a b : Sublocale E) :
    m.caratheodory (a ⊔ b) ≤ m.caratheodory a + m.caratheodory b := by
  have h : ∀ ε > 0, m.caratheodory (a ⊔ b) ≤ m.caratheodory a + m.caratheodory b + 2 * ε := by
    intro ε h
    have h_a : ∃ w ∈ openNhds a, m.toFun w ≤ m.caratheodory a + ε := by
      exact Measure.exists_mem_openNhds_le a ε h
    have h_b : ∃ w ∈ openNhds b, m.toFun w ≤ m.caratheodory b + ε := by
      exact Measure.exists_mem_openNhds_le b ε h
    rcases h_a with ⟨w_a, ⟨ha1, ha2⟩⟩
    rcases h_b with ⟨w_b, ⟨hb1, hb2⟩⟩
    simp only [openNhds, Set.mem_ofPred_eq] at ha1 hb1
    have h1 : m.caratheodory (a ⊔ b) ≤ m.caratheodory ((w_a ⊔ w_b).toSublocale) := by
      apply Measure.caratheodory.mono
      rw [Open.preserves_sup]
      exact sup_le_sup ha1 hb1
    apply le_trans h1
    rw [Measure.caratheodory.open_eq_toFun]
    rw [Measure.strictly_additive]
    simp only [tsub_le_iff_right]
    have h2 : (m.caratheodory a + ε) + (m.caratheodory b +  ε) ≤
        m.caratheodory a + m.caratheodory b + 2 * ε + m.toFun (w_a ⊓ w_b) := by
      ring_nf
      simp only [le_add_iff_nonneg_right, zero_le]
    apply le_trans' h2 <| add_le_add ha2 hb2
  have h2 : m.caratheodory (a ⊔ b) - (m.caratheodory a + m.caratheodory b) ≤
      sInf {ε : NNReal | ε > 0} := by
    apply le_csInf
    · simp only [Set.Nonempty, gt_iff_lt, Set.mem_ofPred_eq]
      use 42
      norm_num
    · intro b1 h1
      simp only [gt_iff_lt, Set.mem_ofPred_eq] at h1
      let h2 := h (b1 / 2) (by exact half_pos h1)
      apply_fun
        (fun x : NNReal ↦ (x - (Measure.caratheodory a + Measure.caratheodory b))) at h2
      · simp only at h2
        have h3 : m.caratheodory a + m.caratheodory b + 2 * (b1 / 2) -
            (m.caratheodory a + m.caratheodory b) = b1 := by
          rw [add_tsub_cancel_left]
          ring
        rw [h3] at h2
        apply h2
      · simp only [Monotone]
        intro a1 b1 h
        exact tsub_le_tsub_right h (Measure.caratheodory a + Measure.caratheodory b)
  rw [sInf_epsilon_eq_zero'] at h2
  exact (tsub_le_iff_right.mp h2).trans (zero_add _).le
