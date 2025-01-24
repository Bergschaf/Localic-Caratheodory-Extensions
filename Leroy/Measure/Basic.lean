import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Sublocales
import Leroy.Further_Topology




lemma sInf_epsilon_eq_zero : sInf {ε : Real | ε > 0} = 0 := by
      apply le_antisymm
      . rw [csInf_le_iff, lowerBounds]
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        intro b h
        exact le_of_forall_le_of_dense h
        simp only [BddBelow, Set.Nonempty, gt_iff_lt]
        use -42
        simp only [lowerBounds, Set.mem_setOf_eq]
        intro b h
        apply le_trans' (le_of_lt h)
        norm_num
        simp [Set.Nonempty]
        use 42
        norm_num

      . apply le_csInf
        simp only [Set.Nonempty, gt_iff_lt, Set.mem_setOf_eq]
        use 42
        norm_num
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        exact fun b a => le_of_lt a

lemma sInf_epsilon_eq_zero' : sInf {ε : NNReal | ε > 0} = 0 := by
      apply le_antisymm
      . rw [csInf_le_iff, lowerBounds]
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        intro b h
        exact le_of_forall_le_of_dense h
        simp only [BddBelow, Set.Nonempty, gt_iff_lt]
        use 0
        simp only [lowerBounds, Set.mem_setOf_eq]
        intro b h
        apply le_trans' (le_of_lt h)
        norm_num
        simp [Set.Nonempty]
        use 42
        norm_num

      . apply le_csInf
        simp only [Set.Nonempty, gt_iff_lt, Set.mem_setOf_eq]
        use 42
        norm_num
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        exact fun b a => le_of_lt a



-----
variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]


def increasingly_filtered {Z : Type*} [PartialOrder Z] (s : Set Z) : Prop :=
  ∀ U ∈ s, ∀ V ∈ s, ∃ W ∈ s, U ≤ W ∧ V ≤ W

def increasing {Z : Type*} [PartialOrder Z] (s : Set Z) : Prop :=
  ∀ U ∈ s, ∃ V ∈ s, U ≤ V

structure Measure where
  toFun : (Open X) → NNReal -- Evtl ENNReal (brauchen wir ⊤)
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Open X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set  (Open X)), increasingly_filtered s → toFun (sSup s) = sSup (toFun '' s)
variable {m : @Measure E e_frm}

def Open_Neighbourhood (u : Sublocale X) : Set (Open X) := {v : Open X | u ≤ v}

def Neighbourhood (u : Sublocale X) : Set (Sublocale X) := {v | ∃ w ∈ Open_Neighbourhood u, w ≤ v}


noncomputable def Measure.caratheodory {m : @Measure X h} (a : Sublocale X) : NNReal :=
  sInf (m.toFun '' Open_Neighbourhood a)



lemma Measure.all_le_top {m : @Measure X h} : ∀ a : Open X, m.toFun a ≤ m.toFun ⊤ := by
  intro a
  apply m.mono
  exact OrderTop.le_top a


lemma Caratheodory_opens {m : @Measure X h} : ∀ x : Open X, m.caratheodory x = m.toFun x := by
  simp [Measure.caratheodory]
  intro x
  simp [Open_Neighbourhood]
  apply le_antisymm
  . apply csInf_le'
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use x
  . rw [le_csInf_iff]
    simp
    intro a h
    exact m.mono x a h
    exact OrderBot.bddBelow (m.toFun '' {v | x ≤ v})
    simp [Set.Nonempty]
    use m.toFun x
    use x

lemma Measure.caratheodory_top {m : @Measure X h} : m.caratheodory ⊤ = m.toFun ⊤ := by
  simp only [caratheodory, Open_Neighbourhood, top_le_iff]
  have h : {v : Open X | v.toSublocale = ⊤} = {⊤} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    have h1 : (⊤ : Open X).toSublocale = ⊤ := by
      exact Open.top_sublocale
    rw [← h1]
    exact StrictMono.apply_eq_top_iff fun ⦃a b⦄ a => a
  rw [h]
  simp only [Set.image_singleton, csInf_singleton]


lemma Caratheodory_monotonic (m : Measure) {A B : Sublocale E} : A ≤ B → m.caratheodory A ≤ m.caratheodory B := by
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

    simp only [Open.top_sublocale, Nucleus.top, Nucleus.toFun_eq_coe, and_true]
    exact fun v => Nucleus.increasing' B
  . simp only [Open_Neighbourhood, Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.image_subset_iff]
    rw [@Set.setOf_subset]
    intro x h1
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    use x
    rw [Sublocale.le_iff] at h
    apply And.intro
    . exact fun v => Preorder.le_trans (x.toSublocale v) (B v) (A v) (h1 v) (h v)
    . rfl

lemma Caratheodory.le_top (m : Measure) : ∀ a : Sublocale E, m.caratheodory a ≤ m.caratheodory ⊤ := by
  intro a
  apply Caratheodory_monotonic
  exact OrderTop.le_top a

lemma le_Neighbourhood {a : Sublocale E} : ∀ x ∈ Neighbourhood a, a ≤ x := by
  intro x h
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_setOf_eq] at h
  rcases h with ⟨w, ⟨h1,h2⟩⟩
  exact Preorder.le_trans a w.toSublocale x h1 h2


lemma Open_Neighbourhood_nonempty (x : Sublocale X) : Nonempty (Open_Neighbourhood x) := by
  simp [Set.Nonempty]
  use ⊤
  rw [Open_Neighbourhood]
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.mem_setOf_eq, Open.top_sublocale]
  exact fun v => Nucleus.increasing' x



lemma Open_Neighbourhood.top_mem {x : Sublocale X}: ⊤ ∈ Open_Neighbourhood x := by
  rw [Open_Neighbourhood]
  simp only [Set.mem_setOf_eq, Open.top_sublocale, le_top]


@[simp]
lemma Open_Neighbourhood.Nonempty {u : Sublocale X} : (Open_Neighbourhood u).Nonempty := by
  rw [Set.Nonempty]
  use ⊤
  exact top_mem

lemma Open_Neighbourhood.inf_closed {x : Sublocale E} : ∀ U ∈ Open_Neighbourhood x, ∀ V ∈ Open_Neighbourhood x, U ⊓ V ∈ Open_Neighbourhood x := by
  sorry

lemma Exists_Neighbourhood_epsilon (a : Sublocale E) : ∀ ε > 0, ∃ w ∈ Open_Neighbourhood a, m.toFun w ≤ m.caratheodory a + ε  := by
      have h_aux (ε : Real) (hε : ε > 0) (s : Set Real) (h : s.Nonempty): ∃ W ∈ s, W < sInf s + ε := by
        refine Real.lt_sInf_add_pos ?_ hε
        exact h

      have h_aux' (ε : Real) (hε : ε > 0) (s : Set NNReal) (h : s.Nonempty): ∃ W ∈ s, W < sInf s + ε := by
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
      let h := h_aux' ε hε (m.toFun '' Open_Neighbourhood a) h_nonempty
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
lemma preserves_sup (m : @Measure X h) {n : ℕpos} (X_n : Fin (n.val) → Sublocale X) (h : increasing (Set.range X_n)) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by

  have h_1 : ∀ (ε : Rpos), ∀ n' : Fin (n.val), ∃ neighbour ∈ Open_Neighbourhood (X_n n'), m.toFun neighbour - m.caratheodory (X_n n') ≤ ε.val / n.val :=  by
    intro ε n'
    have h := @Exists_Neighbourhood_epsilon _ _ m (X_n n') (ε.val / n.val) (by simp_all; sorry)
    rcases h with ⟨w, ⟨h1,h2⟩⟩
    use w
    use h1
    exact tsub_le_iff_left.mpr h2
  let V_n (ε : Rpos) (n' : Fin (n.val)) := Classical.choose (h_1 ε n')
  let W_n (ε : Rpos) (n' : Fin (n.val)) := iSup (fun (m : Fin (n')) ↦ V_n ε ⟨m.val, (by apply lt_trans m.prop n'.prop)⟩)
  let W (ε : Rpos) := iSup (W_n ε)
  have sup_V_n (ε : Rpos) : W ε  = iSup (V_n ε) := by sorry

  have h : ∀ (ε : Rpos), m.caratheodory (W ε) ≤ ε.val + m.caratheodory (iSup X_n) := by
    intro ε
    have h_2 : ∀ n' : Fin (n.val), m.caratheodory (W_n ε n') - m.caratheodory (X_n n') ≤ n' * (ε.val / n.val) := by sorry
    sorry

  apply le_antisymm
  . sorry
  . sorry -- trivial ??


/--
TODO ggf in den Blueprint aufnehmen
-/
lemma Caratheodory_subadditive (a b : Sublocale E ) : m.caratheodory (a ⊔ b) ≤ m.caratheodory a + m.caratheodory b := by
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
      apply Caratheodory_monotonic
      rw [Open.Max_eq]
      exact sup_le_sup ha1 hb1
    apply le_trans h1
    rw [Caratheodory_opens]
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
