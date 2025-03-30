import Leroy.Measure.Regular
import Leroy.Measure.Restrict

variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]

section
variable {E' : Type*} [Order.Frame E']

variable {m : @Measure E' _}

open Sublocale


def e_μ (m : @Measure E' _) (u : E') : E' :=
  (sSup {w : Open E' | u ≤ w ∧ m.toFun w = m.toFun ⟨u⟩}).element

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
  . rw [increasingly_filtered]
    simp_all only [Set.mem_setOf_eq, and_imp]
    intro a h1 h2 b h3 h4
    use a ⊔ b
    . simp [Open.sup_def]
      apply And.intro
      apply And.intro
      · apply le_trans h1 le_sup_left
      . apply le_antisymm
        . rw [← Open.sup_def]
          rw [Measure.strictly_additive]
          rw [h2, h4]
          have h5 : m.toFun ⟨u⟩ ≤ m.toFun (a ⊓ b) := by
            apply Measure.mono
            simp [Open.le_def, h1, h3]
          simp [NNReal.sub_def, Real.toNNReal]

          rw [← Subtype.coe_le_coe]
          simp only [NNReal.val_eq_coe, sup_le_iff, tsub_le_iff_right, add_le_add_iff_left,
            NNReal.coe_le_coe, NNReal.zero_le_coe, and_true]
          exact h5

        . apply Measure.mono
          simp [Open.le_def]
          apply le_trans h1 le_sup_left
      . apply And.intro
        . simp [Open.le_def]
        . simp [Open.le_def]


lemma e_μ_idempotent (m : @Measure E' _) : ∀ (x : E'), e_μ m (e_μ m x) ≤ e_μ m x := by
  intro x
  simp only [e_μ, Open.sSup_def, sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
    and_imp]
  intro a b c d e
  subst e
  --
  apply le_sSup
  simp
  use b
  simp only [and_true]
  apply And.intro
  .
    apply c
    on_goal 3 => {rfl
    }
    · simp_all only [le_refl]
    · simp_all only
  rw [d]
  let h := @e_μ_Measure_eq E' _ m x
  simp [e_μ] at h
  exact h


lemma e_μ_le_apply (m : @Measure E' _) : ∀ (x : E'), x ≤ e_μ m x := by
  intro x
  simp [e_μ, Open.sSup_def]
  apply le_sSup
  simp
  use ⟨x⟩

lemma e_μ_mono (m : @Measure E' _) (x y : E') : x ≤ y → e_μ m x ≤ e_μ m y := by
  intro h
  conv =>
    enter [2]
    simp [e_μ]
  simp only [Open.sSup_def, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
  intro c h3
  let h4 := @h3 (y ⊔ (e_μ m x)) ⟨(y ⊔ (e_μ m x))⟩






lemma e_μ_map_inf (m : @Measure E' _) : ∀ (x y : E'), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y

  apply le_antisymm
  .
    refine le_inf_iff.mpr ?_
    apply And.intro
    . apply e_μ_mono
      simp
    . apply e_μ_mono
      simp

  . simp only [e_μ, ge_iff_le, Open.sSup_def, le_inf_iff]
    rw [sSup_inf_sSup]
    simp only [Set.mem_prod, Set.mem_image, Set.mem_setOf_eq, le_sSup_iff, upperBounds,
      forall_exists_index, and_imp, iSup_le_iff, Prod.forall]
    intro a h1 b c d h2 h3 h4 e h5 h6 h7
    subst h4 h7
    let h1' := @h1 (d ⊓ e) ⟨d ⊓ e⟩
    simp at h1'
    apply h1'
    . exact inf_le_of_left_le h2
    . exact inf_le_of_right_le h5
    . rw [← Open.inf_def]
      apply le_antisymm
      . rw [← Open.inf_def]
        repeat rw [Measure.strictly_additive']
        rw [h3, h6]
        repeat rw [NNReal.sub_def]
        rw [← Subtype.coe_le_coe]
        simp only [NNReal.coe_add, NNReal.val_eq_coe, Real.coe_toNNReal', le_sup_iff, sup_le_iff,
          tsub_le_iff_right, sub_nonneg, zero_add, le_refl, and_true]
        left
        apply And.intro
        . have h1 : (↑(m.toFun { element := x }) : Real) + ↑(m.toFun { element := y }) - ↑(m.toFun ({ element := x } ⊔ { element := y })) +
            ↑(m.toFun (d ⊔ e)) = (↑(m.toFun { element := x }) + ↑(m.toFun { element := y })) + (- ↑(m.toFun ({ element := x } ⊔ { element := y })) +
            ↑(m.toFun (d ⊔ e))) := by
            ring
          rw [h1]
          conv =>
            enter [1]
            rw [← add_zero ((↑(m.toFun { element := x }) : Real) + ↑(m.toFun { element := y }))]
          apply add_le_add
          . rfl
          . simp
            apply Measure.mono
            apply sup_le_sup
            . exact h2
            . exact h5

        . rw [Measure.strictly_additive]
          simp only [NNReal.sub_def, NNReal.coe_add, Real.coe_toNNReal', sup_le_iff,
            tsub_le_iff_right, le_add_iff_nonneg_right, NNReal.zero_le_coe, true_and]
          positivity
      . apply Measure.mono
        rw [← Open.inf_def]
        apply inf_le_inf
        . exact h2
        . exact h5


def μ_Reduction (m : @Measure E' _) : Sublocale E' where
  toFun := e_μ m
  idempotent' x := e_μ_idempotent m x
  le_apply' x := e_μ_le_apply m x
  map_inf' x y := e_μ_map_inf m x y


lemma Measure.μ_Reduction_le_if (m : @Measure E' _) (U : Sublocale E') : (∀ i, m.toFun ⟨U i⟩ = m.toFun ⟨i⟩) → μ_Reduction m ≤ U := by
  intro h i
  simp [μ_Reduction, e_μ, Open.sSup_def]
  apply le_sSup
  simp
  use ⟨U i⟩
  simp_all [U.le_apply, h]


lemma Measure_Neighbourhood_μ_eq_top (m : @Measure E' _) : ∀ V ∈ Open_Neighbourhood (μ_Reduction m), m.toFun V = m.toFun ⊤ := by
  intro V h
  apply le_antisymm
  . simp [Measure.mono]
  have h : ∀ W : E', V.toSublocale W ≤ μ_Reduction m W := by
    simp [Open_Neighbourhood, Sublocale.le_iff, μ_Reduction] at h
    rw [Nucleus.coe_mk, InfHom.coe_mk] at h
    simp
    apply h
  let h1 := h V
  simp [μ_Reduction] at h1
  rw [Nucleus.coe_mk, InfHom.coe_mk] at h1
  have h2 := e_μ_Measure_eq m V
  rw [h1] at h2
  simp at h2
  rw [← h2]
  rw [← Open.top_element]





lemma Measure_μ_Reduction_eq_top (m : @Measure E' _) : m.caratheodory (μ_Reduction m) = m.toFun ⊤ := by
  apply le_antisymm
  . apply Measure.caratheodory.le_top_toFun
  simp [Measure.caratheodory]
  apply le_csInf
  . use m.toFun ⊤
    use ⊤
    simp only [and_true]
    exact Open_Neighbourhood.top_mem
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a h
  apply le_of_eq (Measure_Neighbourhood_μ_eq_top m a h).symm


lemma μ_Reduction_eq_sInf [Fact (regular E')] (m : @Measure E' _) : μ_Reduction m = sInf (Open.toSublocale '' {w : Open E' | m.toFun w = m.toFun ⊤}) := by
  rw [Sublocale.intersection_Open_Neighbourhhood (μ_Reduction _)]
  apply le_antisymm
  . simp only [le_sInf_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro a h
    --
    apply sInf_le
    simp only [Set.mem_image]
    use a
    simp only [Open_Neighbourhood, Set.mem_setOf_eq, and_true]
    ---
    have h1 : ∀ H : Open E', m.toFun (a ⊓ H) = m.toFun H := by
      intro H
      have h2 : m.toFun (a ⊓ H) = m.toFun a + m.toFun H - m.toFun (a ⊔ H) := by
        exact Measure.strictly_additive' a H
      rw [h2]
      have h3 : m.toFun (a ⊔ H) = m.toFun ⊤ := by
        apply le_antisymm
        . exact Measure.all_le_top (a ⊔ H)
        . have h1 : m.toFun (a) ≤ m.toFun (a ⊔ H) := by
            apply Measure.mono
            simp
          apply le_trans' h1
          rw [← h]
      simp [h, h3]
    ----- UUUUU sehr wichtig (ähnlich wie bei lemma 7)
    intro i
    simp [Open.toSublocale]
    let h2 := h1 ⟨a.element ⇨ i⟩
    simp [Open.inf_def] at h2
    let h3 := h1 ⟨i⟩
    simp [Open.inf_def] at h3
    simp [μ_Reduction, e_μ, Open.sSup_def]

    apply le_sSup
    simp
    use ⟨a.element ⇨ i⟩
    simp
    rw [← h2, h3]

  . simp
    intro a h
    apply sInf_le
    simp
    use a
    simp only [and_true]
    exact Measure_Neighbourhood_μ_eq_top m a h

lemma μ_Reduction_eq_sInf_Sublocale [Fact (regular E')] (m : @Measure E' _) : μ_Reduction m = sInf ({w : Sublocale E' | m.caratheodory w = m.toFun ⊤}) := by
  apply le_antisymm
  . rw [μ_Reduction_eq_sInf]

    simp only [le_sInf_iff, Set.mem_setOf_eq, OrderDual.forall]
    intro a h
    rw [csInf_le_iff]
    . simp only [lowerBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, OrderDual.forall]

      intro b h1
      rw [Sublocale.intersection_Open_Neighbourhhood (OrderDual.toDual a)]
      simp [Open_Neighbourhood]
      intro c h2
      apply h1
      apply le_antisymm
      . exact Measure.all_le_top c
      . rw [← h]
        rw [← Measure.caratheodory.open_eq_toFun]
        apply Measure.caratheodory.mono
        exact h2

    . exact OrderBot.bddBelow (Open.toSublocale '' {w | m.toFun w = m.toFun ⊤})
    . use ⊤
      simp_all only [Set.mem_image, Set.mem_setOf_eq]
      apply Exists.intro
      · apply And.intro
        · rfl
        · simp_all only [Open.top_toSublocale]


  . apply csInf_le
    . exact OrderBot.bddBelow {w | Measure.caratheodory w = m.toFun ⊤}
    . simp
      apply Measure_μ_Reduction_eq_top


lemma μ_Reduction_le_of_top [Fact (regular E')] (m : @Measure E' _) (A : Sublocale E') (h : m.caratheodory A = m.toFun ⊤) :
    μ_Reduction m ≤ A := by
  rw [μ_Reduction_eq_sInf_Sublocale]
  apply sInf_le
  . simp [h]




variable [Fact (regular E')]
lemma embed_measure_open (A : Sublocale E') (b : Open (Image A)) : m.caratheodory (A.embed b) = (m.restrict_sublocale_measure A).toFun b := by
  simp [Measure.restrict_sublocale_measure,Measure.restrict_sublocale]


lemma embed_measure (A : Sublocale E') (b : Sublocale (Image A)) : m.caratheodory (A.embed b) = (m.restrict_sublocale_measure A).caratheodory b := by
  apply le_antisymm
  . simp [Measure.restrict_sublocale_measure, Measure.caratheodory, Measure.restrict_sublocale]

    apply le_csInf
    . simp
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    apply le_csInf
    . simp
    . simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro c h1
      simp [Sublocale.Open_Neighbourhood] at h h1
      rw [csInf_le_iff]
      . simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
        intro d h2
        simp only [Open_Neighbourhood, Set.mem_setOf_eq] at h2
        apply h2
        apply le_trans' h1
        apply_fun A.embed at h
        exact h
        exact embed.mono A
      . use 0
        simp [lowerBounds]
      . simp
  . simp [Measure.restrict_sublocale_measure,Measure.caratheodory, Measure.restrict_sublocale]
    apply le_csInf
    . simp
    . simp
      intro a h
      rw [csInf_le_iff]
      simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Set.mem_setOf_eq]
      intro c h1
      .
        conv at h1 =>
          enter [2, 2]
          rw [le_csInf_iff'' (by simp)]
        simp at h1
        ---- Man braucht die restriction für offene
        have h2 : A.restrict_open a ∈ b.Open_Neighbourhood := by
          simp [Open_Neighbourhood] at h ⊢
          apply_fun (. ⊓ A) at h
          simp only at h
          have h_help :  A.embed b ⊓ A  = A.embed b := by
            apply le_antisymm
            . simp
            . simp only [le_inf_iff, le_refl, true_and]
              exact embed_le A b
          rw [h_help] at h
          have h1 := A.restrict_mono _ _ (by simp) (by exact embed_le A b) h
          rw [Sublocale.restrict_embed] at h1
          apply le_trans h1
          rw [Sublocale.restrict_open_eq_restrict]
          apply Sublocale.restrict_mono
          simp
          . rw [Monotone]
            exact fun ⦃a b⦄ a_1 => inf_le_inf_right A a_1
        have h3 := h1 (A.restrict_open a) h2
        --
        apply h3
        rw [embed_restrict_open]
        simp [Open_Neighbourhood]

      . use 0
        simp [lowerBounds]
      . simp


noncomputable def R_μ (A : Sublocale E') : Sublocale E' := A.embed (μ_Reduction (m.restrict_sublocale_measure A))

lemma μ_R_μ_eq (A : Sublocale E') : m.caratheodory A = m.caratheodory (@R_μ _ _ m _ A) := by
  rw [R_μ]
  rw [embed_measure]
  rw [Measure_μ_Reduction_eq_top]
  rw [← Measure.caratheodory.open_eq_toFun]
  rw [← embed_measure]
  rw [Open.top_toSublocale]
  rw [embed_top]


end

variable {ι : Type*} [PartialOrder ι] [Nonempty ι]


def decroissante' (V : ι → Open E) : Prop :=
  ∀ i j : ι, i ≤ j → V j ≤ V i

def decroissante (V : Set (Open E)) : Prop :=
  decroissante' (fun (x : V) ↦ x.val)


def filtrante_decroissante (V : ι → Sublocale E) : Prop :=
  ∀ n m : ι, ∃ l, V l ≤ V n ∧ V l ≤ V m

def filtrante_decroissante' (s : Set (Sublocale E)) : Prop :=
  ∀ n ∈ s, ∀ m ∈ s, ∃ l ∈ s, l ≤ n ∧ l ≤ m

open Sublocale
variable {m : @Measure E _}

/--
Leroy Lemma 6
-/
lemma Measure.preserves_iInf (V_n : ℕ → (Open E)) (h : decroissante' V_n) :
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
    apply Measure.caratheodory.mono
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
      apply Measure.caratheodory.mono
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




lemma ENNReal.tendsto_atTop' {β : Type u_2} [Nonempty β] [SemilatticeSup β] {f : β → ENNReal} {a : ENNReal} (ha : a ≠ ⊤) :
        Filter.Tendsto f Filter.atTop (nhds a) ↔ ∀ ε > 0,(h : ε ≠ ⊤) → ∃ (N : β), ∀ n ≥ N, f n ∈ Set.Icc (a - ε) (a + ε) := by
  apply Iff.intro
  . intro h
    let x := (ENNReal.tendsto_atTop ha).mp h
    intro e he h1
    apply x e he
  . intro h
    have h1 : ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Set.Icc (a - ε) (a + ε) := by
      intro e he
      by_cases hC : e = ⊤
      . subst hC
        simp
      apply h e he hC
    exact (ENNReal.tendsto_atTop ha).mpr h1

def rec' (seq : ℕ → Open E)
  | 0 => seq 0
  | Nat.succ n => seq (n + 1) ⊓ (rec' seq n)

/-- Leroy lemme 7-/
lemma Measure.caratheodordy.preserves_iInf {ι : Type*} [Nonempty ι] (A_i : ι → Sublocale E)  (h : filtrante_decroissante A_i) :
  m.caratheodory (iInf A_i) = iInf (m.caratheodory ∘ A_i) := by

  apply le_antisymm
  . simp only [OrderBot.bddBelow, le_ciInf_iff, Function.comp_apply]
    intro i
    apply Measure.caratheodory.mono
    exact iInf_le A_i i

  let V_a := {w : Open E | ∃ i, w ∈ (A_i i).Open_Neighbourhood}
  have h_V_A_inf_closed (u v : Open E) (h1 : u ∈ V_a) (h2 : v ∈ V_a) : u ⊓ v ∈ V_a := by
    simp [V_a, Sublocale.Open_Neighbourhood] at h1 h2 ⊢
    rcases h1 with ⟨i, h1⟩
    rcases h2 with ⟨j, h2⟩
    rcases h i j with ⟨k, ⟨h3, h4⟩⟩
    use k
    simp [Open.preserves_inf]
    apply And.intro
    . apply le_trans h3 h1
    . apply le_trans h4 h2



  have hvn_1 : iInf A_i = sInf (Open.toSublocale '' V_a) := by
    apply le_antisymm
    . simp
      intro a h
      simp [V_a] at h
      rcases h with ⟨i, h⟩
      simp [Open_Neighbourhood] at h
      exact iInf_le_of_le i h
    simp
    intro i
    have h1 : sInf (Open.toSublocale '' V_a) ≤  sInf (Open.toSublocale '' ((A_i i ).Open_Neighbourhood)) := by
      apply sInf_le_sInf
      refine Set.image_mono ?_
      simp only [V_a]
      refine Set.subset_setOf.mpr ?_
      exact fun x a => Exists.intro i a
    apply le_trans h1
    rw [← @intersection_Open_Neighbourhhood]

  have V_n_nonempty : Nonempty V_a := by
    use ⊤
    simp only [Open_Neighbourhood, Set.mem_setOf_eq, Open.top_toSublocale, le_top, exists_const,
      V_a]

  have hvn_2 : ⨅ i, m.caratheodory (A_i i) = ⨅ w : V_a, m.toFun w := by
    apply le_antisymm
    . apply le_ciInf
      intro x
      simp only [Set.coe_setOf, V_a] at x
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨y, hx⟩
      simp [Open_Neighbourhood] at hx
      refine ciInf_le_of_le ?_ y ?_
      . use 0
        simp [lowerBounds]
      rw [← Measure.caratheodory.open_eq_toFun]
      apply Measure.caratheodory.mono
      apply hx
    apply le_ciInf
    intro i

    rw [← add_zero (m.caratheodory _)]
    rw [← sInf_epsilon_eq_zero']
    rw [← tsub_le_iff_left]
    apply le_csInf
    . use 42
      simp
    simp only [gt_iff_lt, Set.mem_setOf_eq, tsub_le_iff_right, V_a]
    intro b hb
    obtain ⟨w, ⟨hw1, hw2⟩⟩ := (@Exists_Neighbourhood_epsilon _ _ m (A_i i) b (by exact hb))
    refine ciInf_le_of_le ?_ ⟨w, (by use i)⟩ ?_
    . use 0
      simp [lowerBounds]
    simp only [V_a]
    apply le_trans hw2
    rw [add_comm]

  rw [Function.comp_def]
  rw [hvn_2]
  have h_V_a_nonempty : ((m.toFun '' V_a)).Nonempty := by exact Set.Nonempty.of_subtype
  ------------- Wichitig
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_seq_tendsto_sInf (h_V_a_nonempty) (by use 0;simp[lowerBounds])
  -------------
  simp at hu3
  let V_n' (n : ℕ) := Classical.choose (hu3 n)
  let V_n := rec' (fun n ↦ Classical.choose (hu3 n))


  have V_n_decroissante : decroissante' V_n := by
    simp [decroissante']
    intro i j hij
    induction j with
    | zero =>
      simp_all
    | succ j hj =>
      rw [← Nat.succ_eq_add_one, Nat.le_succ_iff] at hij
      cases hij with
      | inl hij =>
        apply le_trans' (hj hij)
        simp [V_n, rec']
      | inr hij =>
        rw [hij]

  have h_iInf_V_n : iInf (m.toFun ∘ V_n') = sInf (m.toFun '' V_a) := by
    have h_help : m.toFun ∘ V_n' = u  := by
      ext x
      simp
      obtain ⟨_, V_n_spec⟩ :=Classical.choose_spec (hu3 x)
      rw [V_n_spec]
    rw [h_help]
    apply_fun ENNReal.ofNNReal
    rw [ENNReal.coe_iInf]
    rw [← Function.comp_def]
    rw [@iInf_eq_of_tendsto ℕ ENNReal _ _ _ _ _  (ENNReal.ofNNReal ∘ u) ↑(sInf (m.toFun '' V_a)) (by apply Monotone.comp_antitone; simp [Monotone]; exact hu1)]

    refine (ENNReal.tendsto_atTop' ?_).mpr ?_
    . simp
    . simp only [gt_iff_lt, ge_iff_le, Function.comp_apply, Set.mem_Icc, tsub_le_iff_right]
      intro e he he1
      ----
      rw [@Metric.tendsto_atTop] at hu2
      obtain ⟨n ,hn ⟩ := hu2 e.toReal (by rw [ENNReal.toReal, ENNReal.toNNReal, WithTop.untop', WithTop.recTopCoe.eq_def];simp; cases e; simp; contradiction; simp; exact ENNReal.coe_pos.mp he)
      use n
      intro n1 hn1
      let hn := hn n1 hn1
      rw [NNReal.dist_eq] at hn
      rw [abs_lt] at hn
      simp at hn
      rcases hn with ⟨hn1 ,hn2⟩
      apply And.intro
      .
        refine ENNReal.coe_le_iff.mpr ?_
        intro p hp
        refine NNReal.coe_le_coe.mp ?_
        apply le_trans (le_of_lt hn1)
        apply_fun ENNReal.toReal at hp
        simp only [ENNReal.coe_toReal, V_a] at hp
        rw [← hp]
        rw [ENNReal.toReal_add]
        simp only [ENNReal.coe_toReal, add_comm, le_refl, V_a]
        . exact ENNReal.coe_ne_top
        . exact he1
      .
        refine ENNReal.coe_le_iff.mpr ?_
        intro p hp
        refine NNReal.coe_le_coe.mp ?_
        rw [@sub_lt_iff_lt_add'] at hn2
        apply le_trans (le_of_lt hn2)
        apply_fun ENNReal.toReal at hp
        simp at hp
        rw [← hp, ENNReal.toReal_add]
        simp only [ENNReal.coe_toReal, le_refl, V_a]
        . exact ENNReal.coe_ne_top
        . exact he1
    . exact ENNReal.coe_injective
  have iInf_V_n'_eq_iInf_V_n : iInf (m.toFun ∘ V_n') = iInf (m.toFun ∘ V_n) := by
    apply le_antisymm
    . apply le_ciInf
      intro n
      rw [h_iInf_V_n]
      rw [csInf_le_iff]
      . simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Set.mem_setOf_eq, Function.comp_apply, V_a]
        intro b hb
        obtain ⟨i, hi⟩ : ∃ i, V_n n ∈ (A_i i).Open_Neighbourhood := by
          simp [V_n]
          induction n with
          | zero =>
            simp [V_a]
            obtain ⟨spec, _⟩ := Classical.choose_spec (hu3 0)
            simp [V_a] at spec
            exact spec
          | succ n hn =>
            simp [Open_Neighbourhood] at hn
            rcases hn with ⟨i,hn⟩
            simp [add_tsub_cancel_right, V_a, V_n, rec', Sublocale.Open_Neighbourhood, Open.preserves_inf]
            obtain ⟨spec2, _⟩ := Classical.choose_spec (hu3 (n + 1))
            simp [V_a] at spec2
            obtain ⟨j, spec2⟩ := spec2
            obtain ⟨k, hk⟩ := (h i j)
            use k
            simp [Open_Neighbourhood] at spec2
            exact And.intro (le_trans hk.right spec2) (le_trans hk.left hn)

        exact hb (V_n n) i hi rfl

      . use 0
        simp [lowerBounds]
      . simp
        use ⊤
        simp [V_a, Sublocale.Open_Neighbourhood]

    . apply le_ciInf
      intro n
      refine ciInf_le_of_le ?_ n ?_
      . use 0
        simp [lowerBounds]
      . simp only [Function.comp_apply, V_n, V_n', V_a]
        cases n
        . simp [rec']
        . simp only [add_tsub_cancel_right, V_a, V_n', V_n, rec']
          apply Measure.mono
          simp
  rw [sInf_image'] at h_iInf_V_n
  rw [← h_iInf_V_n]
  rw [iInf_V_n'_eq_iInf_V_n]
  rw [hvn_1]

  rw [← Measure.preserves_iInf] -- lemme 6
  . let I := (iInf (Open.toSublocale ∘ V_n))
    have hI : (iInf (Open.toSublocale ∘ V_n)) = I := rfl
    rw [hI]
    ---
    rw [μ_R_μ_eq I]



    apply Measure.caratheodory.mono
    ---
    simp
    intro a ha
    --- ....
    have h2 : m.caratheodory (a ⊓ I) = m.caratheodory I := by
      apply le_antisymm
      . apply Measure.caratheodory.mono
        simp

      rw [← hI]
      rw [inf_iInf]
      simp
      conv =>
        enter [2, 1, 1, x]
        rw [← Open.preserves_inf]
      have h_decroissante : decroissante' fun x => a ⊓ V_n x := by
          simp [decroissante']
          intro i j h
          apply le_trans inf_le_right
          apply V_n_decroissante
          exact h

      conv =>
        enter [2]
        rw [← Function.comp_def]

        rw [Measure.preserves_iInf _ h_decroissante]
      apply le_ciInf
      intro n
      simp
      rw [Measure.preserves_iInf]
      rw [← iInf_V_n'_eq_iInf_V_n]
      rw [h_iInf_V_n]
      apply csInf_le
      . apply OrderBot.bddBelow
      . simp
        use a ⊓ V_n n
        simp
        have h_v_n : V_n n ∈ V_a := by
          have spec (n : ℕ):= (Classical.choose_spec (hu3 n)).left


          induction n with
          | zero =>
            simp [V_n, rec']
            exact spec 0

          | succ n hn =>
            simp_rw [V_n, rec']
            simp [V_n] at hn
            apply h_V_A_inf_closed
            . exact spec (n + 1)
            . exact hn




        simp [V_a, Open_Neighbourhood] at ha h_v_n ⊢
        rcases ha with ⟨i, ha⟩
        rcases h_v_n with ⟨j, h_v_n⟩
        rw [Open.preserves_inf]
        rw [filtrante_decroissante] at h
        obtain ⟨l, ⟨h1, h2⟩⟩ := h i j
        use l
        apply le_inf
        . apply le_trans h1 ha
        . apply le_trans h2 h_v_n
      . exact V_n_decroissante


    have test := @embed_measure E _ m _ I (I.restrict (a ⊓ I) (by simp))
    rw [Sublocale.embed_restrict] at test

    have h_help : a.toSublocale ⊓ I ≤ a := by simp
    apply le_trans' h_help

    apply Sublocale.restrict_orderiso I _ _ (by rw [R_μ];exact embed_le I (μ_Reduction (restrict_sublocale_measure I m))) (by simp)
    simp_rw [R_μ]
    rw [Sublocale.restrict_embed]
    have h : Fact (regular (Image I)) := by
      refine { out := ?_ }
      exact Image_regular' I

    apply μ_Reduction_le_of_top
    rw [← test]
    rw [h2]
    simp only [restrict_sublocale_measure, restrict_sublocale, Open.top_toSublocale, V_a, V_n', V_n]
    rw [embed_top]



  . exact V_n_decroissante


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
      apply Measure.caratheodory.mono
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
          apply Measure.caratheodory.mono
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
            apply Measure.caratheodory.mono
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
    have h7 : m.caratheodory (A ⊓ B) + (m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B)) = (m.caratheodory A + m.caratheodory B) := by
      rw [@add_tsub_cancel_iff_le]
      have h : m.caratheodory A ≤ m.caratheodory A + m.caratheodory B := by
        exact le_self_add
      apply le_trans' h
      apply Measure.caratheodory.mono
      exact inf_le_left
    rw [h7]
    rw [add_eq_add_iff_eq_and_eq] <;> simp [Measure.caratheodory, sInf_image']

  . exact add_left_injective (caratheodory (A ⊓ B))

/-
theorem Measure.caratheodory.strictly_additive (A B : Sublocale E) :
  m.caratheodory (A ⊔ B) = m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B) := by -/

lemma Beispiel : False := by sorry

#print axioms Beispiel

#print axioms Measure.caratheodory.strictly_additive
