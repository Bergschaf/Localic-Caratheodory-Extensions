import Leroy.Measure.Regular

variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]
variable {E' : Type*} [Order.Frame E']

--variable {m : @Measure E' _}
variable {m : @Measure E _}

open Sublocale

-- TODO Infrastruktur, dass man Sublocals als Local ansehen kann

def e_μ (m : @Measure E' _) (u : E') : E' := (sSup {w : Open E' | u ≥ w ∧ m.toFun w = m.toFun ⟨u⟩}).element
---                                                                 ^ eigentlich steht hier u ≤ w bei leroy

lemma e_μ_Measure_eq (m : @Measure E' _) (u : E') : m.toFun ⟨e_μ m u⟩ = m.toFun ⟨u⟩ := by
  simp [e_μ, Open.sSup_def]
  rw [← Open.sSup_def]
  rw [Measure.filtered]
  apply le_antisymm
  . rw [csSup_le_iff]
    simp
    intro b x h1 h2 h3
    rw [← h3, h2]
    . simp [BddAbove, upperBounds, Set.Nonempty]
      use m.toFun ⊤
      intro a x h1 h2 h3
      rw [← h3]
      exact Measure.all_le_top x
    . simp [Set.Nonempty]
      use m.toFun ⟨u⟩
      use ⟨u⟩
  . rw [le_csSup_iff]
    simp [upperBounds]
    intro b h
    . exact h ⟨u⟩ (by rfl) (by rfl) (by rfl)
    simp [BddAbove, upperBounds, Set.Nonempty]
    use m.toFun ⟨u⟩
    intro a x h1 h2 h3
    rw [← h3, h2]
    --
    simp [Set.Nonempty]
    use m.toFun ⟨u⟩
    use ⟨u⟩
  . simp only [increasingly_filtered, Set.mem_setOf_eq, and_imp]
    intro v h1 h2 w h4 h5

    use w ⊔ v
    simp [le_refl, and_self, true_and]
    apply And.intro
    · simp_all [Open.sup_def]
    · apply le_antisymm
      . apply Measure.mono
        simp_all only [sup_le_iff]
        apply And.intro
        · exact h4
        · exact h1
      . rw [← h5]
        apply Measure.mono
        exact le_sup_left

lemma e_μ_idempotent (m : @Measure E' _) : ∀ (x : E'), e_μ m (e_μ m x) ≤ e_μ m x := by
  intro x
  simp [e_μ, Open.sSup_def]
  intro b x_1 a a_1 a_2
  subst a_2
  simp_all only

lemma e_μ_le_apply (m : @Measure E' _) : ∀ (x : E'), x ≤ e_μ m x := by
  intro x
  simp [e_μ, Open.sSup_def]
  apply le_sSup
  simp
  use ⟨x⟩

lemma e_μ_map_inf (m : @Measure E' _) : ∀ (x y : E'), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y
  apply le_antisymm
  . simp_all [e_μ, Open.sSup_def]
    apply And.intro
    · intro b x_1 a a_1 a_2 a_3
      subst a_3
      ---
      simp only [le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
        and_imp]
      intro b1 h
      let h' := @h x ⟨x⟩
      simp only [le_refl, forall_const] at h'
      exact le_trans' h' a
    · intro b x_1 a a_1 a_2 a_3
      subst a_3
      simp only [le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
        and_imp]
      intro b1 h
      let h' := @h y ⟨y⟩
      simp only [le_refl, forall_const] at h'
      exact le_trans' h' a_1

  . simp only [e_μ, ge_iff_le, Open.sSup_def, le_inf_iff]
    rw [sSup_inf_sSup]
    simp only [Set.mem_prod, Set.mem_image, Set.mem_setOf_eq, le_sSup_iff, upperBounds,
      forall_exists_index, and_imp, iSup_le_iff, Prod.forall]
    intro a h1 b c d h2 h3 h4 e h5 h6 h7
    subst h4 h7
    let h1' := @h1 (x ⊓ y) ⟨x ⊓ y⟩
    simp only [inf_le_left, inf_le_right, forall_const] at h1'
    apply le_trans' h1'
    apply inf_le_inf <;> simp_all

def μ_Reduction (m : @Measure E' _) : Sublocale E' where
  toFun := e_μ m
  idempotent' x := e_μ_idempotent m x
  le_apply' x := e_μ_le_apply m x
  map_inf' x y := e_μ_map_inf m x y

def Measure_Neighbourhood_μ_eq_top (m : @Measure E' _) : ∀ V ∈ Open_Neighbourhood (μ_Reduction m), m.toFun V = m.toFun ⊤ := by
  intro V h
  apply le_antisymm
  . simp [Measure.mono]
  have h1 : μ_Reduction m V.element = ⊤ := by sorry
  sorry




variable {ι : Type*} [PartialOrder ι] [Nonempty ι]


def decroissante' (V : ι → Open E) : Prop :=
  ∀ i j : ι, i ≤ j → V j ≤ V i

def decroissante (V : Set (Open E')) : Prop :=
  decroissante' (fun (x : V) ↦ x.val)


def filtrante_decroissante (V : ι → Sublocale E) : Prop :=
  ∀ n m : ι, ∃ l, V l ≤ V n ∧ V l ≤ V m

def filtrante_decroissante' (s : Set (Sublocale E)) : Prop :=
  ∀ n ∈ s, ∀ m ∈ s, ∃ l ∈ s, l ≤ n ∧ l ≤ m

/--
Leroy Lemma 6
-/
lemma Measure.preserves_sInf (V_n : ℕ → (Open E)) (h : decroissante' V_n) :
    m.caratheodory (iInf (Open.toSublocale ∘ V_n)) = iInf (m.toFun ∘ V_n) := by
  let I :=  (iInf (Open.toSublocale ∘ V_n))

  let F_n (n : ℕ) := Closed.toSublocale (Open.compl (V_n n))
  let G := iSup (F_n)

  have h_ : G ⊔ I = ⊤ := by
    simp [G, I, F_n, iSup,iInf]
    rw [@sup_sInf_eq]
    simp [iInf]
    intro a
    rw [eq_top_iff]
    simp
    rw [eq_top_iff]
    simp
    intro a1 h1
    apply eq_top_iff.mpr
    have h2 : (V_n a1).compl.toSublocale ⊔ a ≤ sSup (Set.range fun n => (V_n n).compl.toSublocale) ⊔ OrderDual.toDual a := by
      simp only [sup_le_iff, I, F_n, G]
      subst h1
      apply And.intro
      · refine le_sup_of_le_left ?_
        apply le_sSup
        simp only [Set.mem_range, exists_apply_eq_apply, I, F_n, G]
      · exact le_sup_right
    apply le_trans' h2
    have h3 : a = (V_n a1).toSublocale := by exact id (Eq.symm h1)
    rw [h3]
    rw [sup_comm]
    rw [Open.sup_compl_eq_top]

  apply le_antisymm
  . simp [iInf]
    apply le_csInf
    . exact Set.range_nonempty (m.toFun ∘ V_n)
    simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff, I,
      F_n, G]
    intro n
    rw [← Measure.caratheodory.open_eq_toFun]
    apply Measure.caratheodory.monotonic
    apply sInf_le
    simp only [Set.mem_range, Function.comp_apply, exists_apply_eq_apply, I, F_n, G]

  have h1 : m.caratheodory ⊤ ≤ m.caratheodory I + m.caratheodory G := by
    rw [← h_]
    rw [sup_comm]
    exact Measure.caratheodory.subadditive I G

  have h1_ : m.caratheodory ⊤ - m.caratheodory G ≤ m.caratheodory I := by
    exact
      (OrderedSub.tsub_le_iff_right (Measure.caratheodory ⊤) (Measure.caratheodory G)
            (Measure.caratheodory I)).mpr
        h1

  have h2 : m.caratheodory G = iSup (m.caratheodory ∘ F_n) := by
    apply le_antisymm
    . simp [iSup, G]
      rw [le_csSup_iff]
      . simp [upperBounds]
        intro b h2
        have h : increasing' F_n := by
          simp [increasing, F_n]
          intro a
          simp [decroissante'] at h
          rw [← Closed.le_iff]
          rw [Closed.le_def]
          simp
          exact h _ _ (Nat.le_add_right _ _)
        rw [sSup_range]
        rw [Measure.caratheodory.preserves_sup']
        apply ciSup_le
        exact h2
        exact h
      . simp [BddAbove, upperBounds, Set.Nonempty]
        use m.caratheodory ⊤
        exact fun a => Measure.caratheodory.le_top m (F_n a)
      . exact Set.range_nonempty (Measure.caratheodory ∘ F_n)

    . simp [iSup]
      apply csSup_le
      . exact Set.range_nonempty (Measure.caratheodory ∘ F_n)
      simp
      intro n
      apply Measure.caratheodory.monotonic
      apply le_sSup
      simp only [Set.mem_range, exists_apply_eq_apply, I, F_n, G]

  have h3 : ⨅ n : ℕ, (m.toFun ⊤ - m.caratheodory (F_n n)) ≤ m.caratheodory I := by
    apply le_trans' h1_
    have h_help (a : NNReal) (f : ℕ → (NNReal)) (hf : BddAbove (Set.range fun i => f i)):  a - ⨆ i, f i = ⨅ i, a - f i:= by
      apply_fun (ENNReal.ofNNReal)
      . simp
        rw [@ENNReal.coe_iInf]
        simp
        rw [ENNReal.coe_iSup]

        refine ENNReal.sub_iSup ?_
        . exact ENNReal.coe_ne_top
        exact hf
      . exact ENNReal.coe_injective

    rw [← h_help]
    rw [← Measure.caratheodory.open_eq_toFun]
    simp only [Open.top_toSublocale]
    apply tsub_le_tsub
    . rfl
    . rw [h2]
      rfl

    simp [BddAbove, upperBounds, Set.Nonempty]
    use m.caratheodory ⊤
    exact fun a => Measure.caratheodory.le_top m (F_n a)

  have h4 : ⨅ n : ℕ, (m.toFun ⊤ - m.caratheodory (F_n n)) = iInf (m.toFun ∘ V_n)  := by
    simp [F_n, iInf]
    have h5 : Set.range (fun n => (m.toFun ⊤) - m.caratheodory (V_n n).compl.toSublocale) = (Set.range (m.toFun ∘ V_n)) := by
      rw [Set.range_eq_iff]
      simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff,
        I, F_n, G]
      apply And.intro
      . intro n
        use n
        rw [← Measure.add_complement (V_n n)]
        simp only [add_tsub_cancel_right, I, F_n, G]
      . intro n
        use n
        rw [← Measure.add_complement (V_n n)]
        simp only [add_tsub_cancel_right, I, F_n, G]

    rw [h5]
  simp_rw [h4, I] at h3
  exact h3


/-- Leroy lemme 7-/
lemma Measure.caratheodordy.preserves_iInf (A_i : ι → Sublocale E) (h : filtrante_decroissante A_i) :
  m.caratheodory (iInf A_i) = iInf (m.caratheodory ∘ A_i) := by

  let V_n' := Set.range fun n => (Sublocale.Open_Neighbourhood (A_i n))
  let V_n : ι → (Open E) := sorry --  TODO flatten V_n

  have h1 : iInf V_n = iInf A_i := by sorry

  --have h2 : ⨅ v_n ∈ V_n, m.toFun v_n = iInf (m.caratheodory ∘ A_i) := by
  --  sorry

  let α_n : ℕ → ι := sorry

  -- have h3 : limit n → ∞, m.toFun (V_n α_n n) = iInf (m.caratheodory ∘ A_i)

  let I := ⨅ n : ℕ, V_n (α_n n)

  let lambda := m.caratheodory I

  have h4 : iInf V_n ≤ I := by sorry

  --- TODO μ Reduction
  sorry


lemma Measure.caratheodory.preserves_sInf (s : Set (Sublocale E)) (h : filtrante_decroissante' s) :
  m.caratheodory (sInf s) = ⨅ x : s, m.caratheodory x := by sorry



theorem Measure.caratheodory.strictly_additive (A B : Sublocale E) :
    m.caratheodory (A ⊔ B) = m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B) := by

  have h_n_1 : Nonempty ↑A.Open_Neighbourhood := Nonempty_Open_Neighbourhood A
  have h_n_2 : Nonempty ↑B.Open_Neighbourhood := Nonempty_Open_Neighbourhood B
  have h_n_3 : Nonempty ↑(A ⊔ B).Open_Neighbourhood := Nonempty_Open_Neighbourhood (A ⊔ B)
  have h_n_4 : Nonempty ↑(A ⊓ B).Open_Neighbourhood := Nonempty_Open_Neighbourhood (A ⊓ B)
  have h_n_5 : Nonempty ↑(A ⊓ B).Neighbourhood := Nonempty_Neighbourhood (A ⊓ B)

  have h1 : m.caratheodory (A ⊔ B) = ⨅ v_a : Open_Neighbourhood A, ⨅ w_b : Open_Neighbourhood B, m.toFun (v_a ⊔ w_b) := by
    apply le_antisymm
    . simp [le_ciInf_iff]
      intro a ha b hb
      rw [← Measure.caratheodory.open_eq_toFun]
      apply Measure.caratheodory.monotonic
      rw [Open.preserves_sup]
      exact sup_le_sup ha hb
    .
      simp only [caratheodory]
      rw [sInf_image']
      simp [le_ciInf_iff]
      intro a ha
      --
      refine ciInf_le_of_le ?_ ⟨a, (by simp [Sublocale.Open_Neighbourhood]; apply le_trans' ha; exact le_sup_left)⟩ ?_
      . use 0
        simp only [lowerBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, zero_le, implies_true]
      refine ciInf_le_of_le ?_ ⟨a, (by simp [Sublocale.Open_Neighbourhood]; apply le_trans' ha; exact le_sup_right)⟩ ?_
      . use 0
        simp only [lowerBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, zero_le, implies_true]
      apply Measure.mono
      simp only [le_refl, sup_of_le_left]

  have h2 : m.caratheodory (A ⊓ B) = ⨅ v_a : Open_Neighbourhood A, ⨅ w_b : Open_Neighbourhood B, m.toFun (v_a ⊓ w_b) := by

    apply_fun ENNReal.ofNNReal
    rw [ENNReal.coe_iInf]
    conv =>
      enter [2, 1, a]
      rw [ENNReal.coe_iInf]
    rw [iInf_prod']
    . rw [← ENNReal.coe_iInf]
      simp only [ENNReal.coe_inj]
      rw [Sublocale.intersection_Neighbourhood A]
      rw [Sublocale.intersection_Neighbourhood B]
      repeat rw [sInf_eq_iInf]
      repeat rw [iInf_subtype']
      have h_n : Nonempty (Subtype (Membership.mem A.Neighbourhood)) := by exact Nonempty_Neighbourhood A
      have h_n' : Nonempty (Subtype (Membership.mem B.Neighbourhood)) := by exact Nonempty_Neighbourhood B
      rw [iInf_inf]
      conv =>
        enter [1, 1, 1, x]
        rw [inf_iInf]
      rw [iInf_prod']
      rw [Measure.caratheodordy.preserves_iInf]
      . rw [Function.comp_def]
        apply le_antisymm
        . repeat rw [← @sInf_eq_iInf', ← @intersection_Neighbourhood]
          rw [@le_ciInf_iff']
          simp only [Prod.forall, Subtype.forall]
          intro a ha b hb
          refine ciInf_le_of_le ?_ ⟨⟨a, (by simp [Neighbourhood]; use a)⟩,⟨b, (by simp [Neighbourhood]; use b)⟩⟩ ?_
          . use 0
            simp [lowerBounds]
          simp only
          rw [← Measure.caratheodory.open_eq_toFun]
          apply Measure.caratheodory.monotonic
          rw [Open.preserves_inf]

        . simp [le_ciInf_iff]
          intro a ha b hb
          simp [Sublocale.Neighbourhood] at ha hb
          rcases ha with ⟨a', ⟨ha1, ha2⟩⟩
          rcases hb with ⟨b', ⟨hb1, hb2⟩⟩
          refine ciInf_le_of_le ?_ ⟨⟨a', (by rw [← @sInf_eq_iInf', ← Sublocale.intersection_Neighbourhood]; exact ha1)⟩, ⟨b', (by rw [← @sInf_eq_iInf', ← Sublocale.intersection_Neighbourhood]; exact hb1)⟩⟩ ?_
          . use 0
            simp [lowerBounds]
          . simp
            rw [← Measure.caratheodory.open_eq_toFun]
            apply Measure.caratheodory.monotonic
            simp [Open.preserves_inf]
            exact ⟨(by exact inf_le_of_left_le ha2),(by exact inf_le_of_right_le hb2)⟩

      . simp only [filtrante_decroissante, le_inf_iff, Prod.exists, Subtype.exists, exists_and_left,
        exists_prop, OrderDual.exists, Prod.forall, Subtype.forall, OrderDual.forall]
        intro a1 h1 a2 h2 a3 h3 a4 h4
        use a1 ⊔ a3
        simp only [toDual_sup]
        refine ⟨(by exact
          Neighbourhood.inf_closed A (OrderDual.toDual a1) h1 (OrderDual.toDual a3) h3), ?_⟩
        use a2 ⊔ a4
        apply And.intro
        . apply And.intro
          . apply inf_le_of_left_le
            apply inf_le_of_left_le
            rfl
          . apply inf_le_of_right_le
            apply inf_le_of_left_le
            rfl
        . apply And.intro
          . apply inf_le_of_left_le
            apply inf_le_of_right_le
            rfl
          . apply And.intro
            . apply Neighbourhood.inf_closed
              exact h2
              exact h4
            . apply inf_le_of_right_le
              apply inf_le_of_right_le
              rfl
    . exact ENNReal.coe_injective


  apply_fun (. + m.caratheodory (A ⊓ B))
  . ring_nf
    have h3 : m.caratheodory (A ⊔ B) + m.caratheodory (A ⊓ B) = ⨅ v_a : Open_Neighbourhood A, ⨅ w_b : Open_Neighbourhood B,  m.toFun (v_a ⊔ w_b) +  m.toFun (v_a ⊓ w_b) := by
      conv =>
        enter [1]
        rw [h1, h2]

      apply_fun ENNReal.ofNNReal
      . simp only [ENNReal.coe_add, ENNReal.coe_sub]

        repeat rw [ENNReal.coe_iInf]
        conv =>
          enter [1, 1, 1, a]
          rw [ENNReal.coe_iInf]
        conv =>
          enter [1, 2, 1, a]
          rw [ENNReal.coe_iInf]
        rw [@ENNReal.iInf_add]
        conv =>
          enter [1, 1, i]
          rw [@ENNReal.iInf_add]
        conv =>
          enter [1, 1, i, 1, i]
          rw [@ENNReal.add_iInf]
        conv =>
          enter [1, 1, i, 1, i, 1, b]
          rw [@ENNReal.add_iInf]
        conv =>
          enter [2, 1, a]
          rw [ENNReal.coe_iInf]
        apply le_antisymm
        . simp_all only [nonempty_subtype, ENNReal.coe_add, le_iInf_iff, iInf_le_iff,
          Subtype.forall, Subtype.coe_prop, implies_true]
        . simp_all only [nonempty_subtype, ENNReal.coe_add, le_iInf_iff, iInf_le_iff,
          Subtype.forall]
          intro a b a_1 b_1 a_2 b_2 a_3 b_3 b_4 a_4
          obtain ⟨w, h⟩ := h_n_1
          obtain ⟨w_1, h_1⟩ := h_n_2
          let h1 := a_4 a b a_1 b_1
          let h2 := a_4 a_2 b_2 a_3 b_3
          let h3 := a_4 (a ⊓ a_2) (by exact Open_Neighbourhood.inf_closed a b a_2 b_2) (a_1 ⊓ a_3) (by exact Open_Neighbourhood.inf_closed a_1 b_1 a_3 b_3)
          apply le_trans h3
          apply add_le_add
          . norm_cast
            apply Measure.mono
            apply sup_le_sup inf_le_left inf_le_left
          . norm_cast
            apply Measure.mono
            apply inf_le_inf inf_le_right inf_le_right
      exact ENNReal.coe_injective
    rw [h3]
    have h5 : ∀ a b : Open E, m.toFun (a ⊔ b) + m.toFun (a ⊓ b) = m.toFun a + m.toFun b := by
      intro a b
      rw [add_comm]
      rw [m.strictly_additive]
      rw [@add_tsub_cancel_iff_le]
      have h : m.toFun a ≤ m.toFun a + m.toFun b := by
        simp
      apply le_trans' h
      apply Measure.mono
      exact inf_le_left
    conv =>
      enter [1, 1, v_a, 1, w_b]
      rw [h5]
    have h6 : ⨅ v_a : Open_Neighbourhood A, ⨅ w_b : Open_Neighbourhood B, m.toFun ↑v_a + m.toFun ↑w_b  =
        (⨅ v_a : Open_Neighbourhood A, m.toFun ↑v_a) +  ⨅ w_b : Open_Neighbourhood B, m.toFun ↑w_b := by
      rw [@NNReal.eq_iff]
      simp [NNReal.coe_iInf]
      rw [ciInf_add]
      conv =>
        enter [2, 1, i]
        rw [add_ciInf (by use 0; simp[lowerBounds])]
      use 0
      simp [lowerBounds]
    rw [h6]
    have h7 : m.caratheodory (A ⊓ B) + (m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B)) = (m.caratheodory A + m.caratheodory B) := by sorry
    rw [h7]
    rw [add_eq_add_iff_eq_and_eq] <;> simp [Measure.caratheodory, sInf_image']

  . exact add_left_injective (caratheodory (A ⊓ B))


section
open Lean Elab Command

namespace CollectAxiomBlame

structure State where
  visited : NameSet      := {}
  axioms  : NameMap (List Name) := {}

abbrev M := ReaderT Environment $ StateM State

partial def collect (src : List Name) (c : Name) : M Unit := do
  let collectExpr (src' : List Name) (e : Expr) : M Unit := e.getUsedConstants.forM (collect src')
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    let src' := c :: src
    match env.find? c with
    | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with axioms := s.axioms.insert c src' }
    | some (ConstantInfo.defnInfo v)   => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.thmInfo v)    => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.opaqueInfo v) => collectExpr src' v.type *> collectExpr src' v.value
    | some (ConstantInfo.quotInfo _)   => pure ()
    | some (ConstantInfo.ctorInfo v)   => collectExpr src' v.type
    | some (ConstantInfo.recInfo v)    => collectExpr src' v.type
    | some (ConstantInfo.inductInfo v) => collectExpr src' v.type *> v.ctors.forM (collect src')
    | none                             => pure ()

end CollectAxiomBlame

elab "#axiom_blame " id:ident : command => Elab.Command.liftTermElabM do
  let n ← Elab.realizeGlobalConstNoOverloadWithInfo id
  Elab.addCompletionInfo <| .id id id.getId (danglingDot := false) {} none
  let env ← getEnv
  let (_, s) := ((CollectAxiomBlame.collect [] n).run env).run {}
  if s.axioms.isEmpty then
    logInfo m!"'{n}' does not depend on any axioms"
  else
    let mut msgs := #[]
    for (ax, decls) in s.axioms do
      msgs := msgs.push m!"* {ax}: {MessageData.joinSep decls.reverse " → "}"
    logInfo m!"'{n}' depends on axioms:\n\n{MessageData.joinSep msgs.toList "\n\n"}"
  logInfo m!"{n}"

#axiom_blame Measure.inf_filtered


end
