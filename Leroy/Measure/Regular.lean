import Leroy.Measure.Basic
import Mathlib.Algebra.Order.Group.CompleteLattice

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]


def well_inside (U V : Open E) := U.closure ≤ V.toSublocale

infix:100 " ≪ " => well_inside





/--
Stone spaces s.80
und auch Sketches of an Elephant 501...
-/
def well_inside_iff (U V : Open E) : U ≪ V ↔ ∃ c, c ⊓ U = ⊥ ∧ c ⊔ V = ⊤ := by
  rw [well_inside]
  apply Iff.intro
  . intro h
    use U.exterior
    apply And.intro
    . rw [inf_comm]
      exact Open.inf_Exterior_eq_bot U
    . -- TODO vlt als extra lemma
      have h_nonempty : Nonempty { x // x ⊓ U = ⊥ } := by use ⊥; simp
      simp [Open.exterior, sSup_eq_iSup']
      rw [iSup_sup, eq_top_iff, le_iSup_iff]
      simp only [sup_le_iff, Subtype.forall, top_le_iff]
      intro b h1
      have h2 : U.exterior ⊔ V = ⊤ := by
        rw [Open.eq_iff, Open.preserves_sup, Open.top_toSublocale]
        rw [sup_eq_top_iff_compl_le]
        apply le_trans' h
        -- TODO vlt als extra lemma
        simp only [Closed.toSublocale, complement, Open.exterior, Open.sSup_def, Open.compl_element,
          Open.closure, Sublocale.le_iff, Open.toSublocale_apply, le_himp_iff, Closed.sInf_def]
        repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
        simp only [sup_le_iff, sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, le_sup_right, and_true]
        intro i a h2
        rw [Nucleus.coe_mk, InfHom.coe_mk] at h2
        --
        have h_nonempty : Nonempty ↑(Open.element '' {z | z ⊓ U = ⊥}) := by
          use ⊥
          use ⊥
          simp only [Set.mem_setOf_eq, bot_le, inf_of_le_left, Open.bot_element, and_self]
        rw [sSup_eq_iSup']
        rw [iSup_sup]
        simp [le_iSup_iff]
        intro b1 h3
        conv at h2 =>
          enter [2, 1]
          rw [inf_sup_right]
        simp only [sup_le_iff, inf_le_left, and_true] at h2
        let h3 := h3 ⟨a.element⟩ (by exact le_bot_iff.mp (h2 ⊥))
        simp only at h3
        exact h3.left
      rw [eq_top_iff, ← h2,sup_le_iff]
      apply h1
      rw [inf_comm]
      exact Open.inf_Exterior_eq_bot U
  . intro h
    rcases h with ⟨c, ⟨h1, h2⟩⟩
    let h1' := h1
    rw [Open.eq_iff, Open.preserves_inf, Open.bot_toSublocale, inf_eq_bot_iff_le_compl] at h1'
    let h2' := h2
    rw [Open.eq_iff, Open.preserves_sup, Open.top_toSublocale, sup_eq_top_iff_compl_le] at h2'
    apply le_trans' h2'
    simp only [Open.closure, Closed.preserves_sInf, sInf_le_iff, lowerBounds, Set.mem_image,
      Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OrderDual.forall]
    intro a h
    apply h
    exact h1'

/-
def well_inside_iff' (U V : Open E) : U ≪ V ↔ V ⊔ ⟨V.elementᶜ⟩ = ⊤ := by
  sorry-/
/--
Leroy definition
Steht auch in Sketches of an Elephant 501
-/
def regular (E : Type*)  [Order.Frame E]: Prop :=
  ∀ (U : Open E), U = sSup {V : Open E | V ≪ U}


variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]

variable {m : @Measure E e_frm}(X_n : ℕ → Sublocale E)

/-
TODO eigene tactic, die Nucleus.coe_mk und sowas simplified
-/
-- Zeigt in Kombination mit Sublocale.eq_intersection_open_closed, dass die Sublocale die intersection der Open_Neigbourhood ist
-- Elephant S.501
lemma Closed.eq_intersection_opens (U : Open E) : U.compl.toSublocale = ⨅ V : Open E, ⨅ _ : V ≪ U, (⟨V.elementᶜ⟩ : Open E).toSublocale := by
  apply le_antisymm
  . simp only [le_iInf_iff]
    intro i h
    let h1 := h
    rw [well_inside] at h1
    rw [well_inside_iff] at h
    rw [Open.compl_element_eq_exterior] --- uuuuuu
    -- vlt woanders...

    simp [Open.compl, Closed.toSublocale, complement, Open.exterior, Open.sSup_def, Open.toSublocale, Sublocale.le_iff]
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
    intro j
    simp [himp_eq_sSup]
    intro b h2
    rw [inf_sSup_eq] at h2
    simp at h2
    rcases h with ⟨w, ⟨hw1, hw2⟩⟩
    let h3 := h2 w hw1
    apply_fun (U.element ⊔ .) at h3
    . simp only at h3
      rw [sup_inf_left] at h3
      have h4 : U.element ⊔ w.element = ⊤ := by
        simp [Open.sup_def, Open.ext_iff] at hw2
        rw [sup_comm]
        exact hw2
      rw [h4] at h3
      simp only [le_top, inf_of_le_left, sup_le_iff, le_sup_left, true_and] at h3
      exact h3
    . rw [Monotone]
      exact fun ⦃a b⦄ a_1 => sup_le_sup_left a_1 U.element
  .
    have h1 : ⨅ V, ⨅ (_ : V ≪ U), ({ element := V.elementᶜ } : Open E).toSublocale ≤ ⨅ V, ⨅ (_ : V ≪ U), V.compl.toSublocale := by
      apply iInf₂_mono
      intro i h
      exact compl_element_le_compl i

    apply le_trans h1
    conv =>
      enter [2]
      rw [e_regular.elim U]
    simp [Open.sSup_def, Open.compl, Closed.toSublocale, complement, Sublocale.le_iff]
    intro i
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
    simp
    refine ⟨?_ , Nucleus.le_apply⟩
    simp [iInf, sInf]
    rw [Nucleus.sSup_apply]
    simp [upperBounds]
    intro a ha j h1
    conv at h1 =>
      enter [2, 2]
      rw [← Nucleus.coe_le_coe]
      simp only [Nucleus.coe_mk, InfHom.coe_mk]
      simp [LE.le]
    exact (h1 a ha i).left

lemma Sublocale.intersection_Opens (a : Sublocale E) : ∃ s : Set (Open E), a = sInf (Open.toSublocale '' s) := by
  use (Set.range (fun x : {w : E × Open E | w.snd ≪ { element := a w.fst }} ↦ ((⟨x.val.fst⟩ : Open E) ⊔ ⟨x.val.sndᶜ⟩)))
  conv =>
    enter [1]
    rw [Sublocale.eq_intersection_open_closed a]

  have h_help (a_1 : E): ({ element := a a_1 } : Closed E) = ({ element := a a_1 } : Open E).compl := by
    simp [Open.compl]
  conv =>
    enter [1, 1, a, 2]
    rw [h_help a]
    rw [Closed.eq_intersection_opens]

  conv =>
    enter [1, 1, a]
    rw [sup_iInf₂_eq]
  conv =>
    enter [1, 1, a, 1, i, 1, j]
    rw [← Open.preserves_sup]


  have h_help : ⨅ (a_1 : E), ⨅ (i : Open E), ⨅ (_ : i ≪ { element := a a_1 }), (({ element := a_1 } : Open E) ⊔ { element := i.elementᶜ }).toSublocale =
        sInf (Open.toSublocale '' Set.range (fun x : {w : E × Open E | w.snd ≪ { element := a w.fst }} ↦ ((⟨x.val.fst⟩ : Open E) ⊔ ⟨x.val.sndᶜ⟩))) := by
      simp [sInf_image]
      conv =>
        enter [2, 1, a, 1, i, 1, i]
        rw [iInf_and]
      apply le_antisymm
      . simp only [le_iInf_iff, iInf_le_iff, OrderDual.forall]
        intro i i_1 i_2 i_3 i_4 a_1 a_2
        subst i_4
        simp_all only
      . simp only [le_iInf_iff, iInf_le_iff, OrderDual.forall]
        intro i i_1 i_2 a_1 a_2
        apply a_2
        on_goal 2 => {rfl
        }
        · simp_all only
  rw [h_help]


/--
Leroy Lemme 2.2
TODO stone spaces als quelle vlt
Seite 81. 1.2
Maybe depends on:
Nucleus.eq_join_open_closed
-/
lemma Sublocale.intersection_Open_Neighbourhhood (a : Sublocale E) : a = sInf (Open.toSublocale '' Sublocale.Open_Neighbourhood a) := by
  apply le_antisymm
  . simp
    exact fun a_1 a => a
  . obtain ⟨s, h1⟩ := Sublocale.intersection_Opens a
    conv =>
      enter [2]
      rw [h1]
    simp only [Open_Neighbourhood, le_sInf_iff, Set.mem_image, sInf_le_iff, lowerBounds,
      Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OrderDual.forall]
    intro a1 ha1 a2 h2
    apply h2
    rw [h1]
    apply sInf_le
    exact Set.mem_image_of_mem Open.toSublocale ha1


lemma Sublocale.intersection_Neighbourhood (a : Sublocale E) : a = sInf (Sublocale.Neighbourhood a) := by
  apply le_antisymm
  . apply le_sInf
    exact fun b a_1 => Sublocale.Neighourhood.le b a_1
  . conv =>
      enter [2]
      rw [Sublocale.intersection_Open_Neighbourhhood a]
    refine sInf_le_sInf ?_
    simp only [Open_Neighbourhood, Neighbourhood, Set.mem_setOf_eq, Set.image_subset_iff,
      Set.preimage_setOf_eq, Set.setOf_subset_setOf]
    intro a_1 a_2
    apply Exists.intro
    · apply And.intro
      on_goal 2 => {rfl}
      · simp_all only
/--
Leroy Lemme 3
-/
lemma Measure.add_complement (U : Open E) : m.toFun U + m.caratheodory (U.compl) = m.toFun (⊤ : Open E) := by

  apply le_antisymm
  .
    let V_a := Sublocale.Open_Neighbourhood (complement U)
    let W_a := Open.exterior '' V_a
    have sSup_W_a_eq_U : sSup W_a = U := by
      rw [e_regular.elim U]
      apply le_antisymm
      . simp [le_sSup_iff, upperBounds, W_a, V_a]
        intro b h a ha
        simp only [Sublocale.Open_Neighbourhood, Set.mem_setOf_eq, V_a, W_a] at ha
        have h1 : a.exterior ≪ U := by
          refine (well_inside_iff a.exterior U).mpr ?_
          use a
          refine ⟨(by exact Open.inf_Exterior_eq_bot a), ?_⟩
          rw [sup_comm]
          rw [Open.eq_iff, Open.preserves_sup, Open.top_toSublocale]
          rw [@sup_eq_top_iff_compl_le]
          exact ha
        exact h h1

      . simp only [Sublocale.Open_Neighbourhood, le_sSup_iff, upperBounds, Set.mem_image,
        Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff, W_a,
        V_a]
        intro b h b1 h2
        let h2' := h2
        rw [well_inside] at h2'
        rw [well_inside_iff] at h2
        rcases h2 with ⟨c, ⟨h2, h3⟩⟩
        let h' := h b1.exterior
        apply le_trans (Open.le_exterior_exterior _)
        apply h'
        rw [← Closure_compl_eq_exterior]
        apply Open_compl_le_Closed_compl
        apply h2'

    apply_fun m.caratheodory at sSup_W_a_eq_U
    have W_a_filtered_croissant : increasingly_filtered W_a := by
      rw [increasingly_filtered]
      intro u hu v hv
      rcases hu with ⟨u1, ⟨hu1, hu2⟩⟩
      rcases hv with ⟨v1, ⟨hv1, hv2⟩⟩
      simp [W_a, V_a]
      use u1 ⊓ v1
      apply And.intro
      . exact Sublocale.Open_Neighbourhood.inf_closed u1 hu1 v1 hv1
      . apply And.intro
        .
          simp [← hu2,← Open.compl_element_eq_exterior, Open.le_def, Open.inf_def]
          apply le_trans' compl_sup_compl_le
          --- genial ^^^
          exact le_sup_left
        . simp [← hv2,← Open.compl_element_eq_exterior, Open.le_def, Open.inf_def]
          apply le_trans' compl_sup_compl_le
          --- genial ^^^
          exact le_sup_right
    have h1 : ∀ v_a ∈ V_a, m.toFun (v_a.exterior) + m.toFun v_a ≤ m.caratheodory ⊤ := by
      intro v_a h_v_a
      have h : m.toFun v_a.exterior + m.toFun v_a = m.toFun v_a.exterior + m.toFun v_a - m.toFun (v_a.exterior ⊓ v_a) := by
        have h1 :  m.toFun (v_a.exterior ⊓ v_a) = 0 := by
          rw [inf_comm]
          rw [@Open.inf_Exterior_eq_bot]
          exact m.empty
        conv =>
          enter [1]
          rw [← tsub_zero (m.toFun v_a.exterior + m.toFun v_a)]
          rw [← h1]
      rw [h]
      rw [← @strictly_additive]
      have h1 : v_a.exterior ⊔ v_a ≤ ⊤ := by
        simp only [le_top]
      apply_fun m.toFun at h1
      rw [Measure.caratheodory.top_eq_toFun]
      exact h1
      apply Measure.mono

    have h2 : ∀ v_a ∈ V_a, m.caratheodory (U.compl) ≤ m.toFun v_a := by
      intro va hva
      simp [V_a, Sublocale.Open_Neighbourhood] at hva

      apply_fun m.caratheodory at hva
      rw [Measure.caratheodory.open_eq_toFun] at hva
      exact hva
      rw [Monotone]
      exact fun ⦃a b⦄ a_1 => caratheodory.monotonic a_1
    rw [Measure.caratheodory.top_eq_toFun] at h1
    have h3 : ∀ v_a ∈ V_a, m.toFun v_a.exterior + m.caratheodory (U.compl) ≤ m.toFun ⊤ := by
      intro va hva
      exact add_le_of_add_le_left (h1 va hva) (h2 va hva)

    have h4 : m.toFun (sSup W_a) + m.caratheodory (U.compl) ≤ m.toFun ⊤ := by
      rw [m.filtered _ W_a_filtered_croissant]
      apply add_le_of_le_tsub_right_of_le
      . rw [← Measure.caratheodory.top_eq_toFun]
        exact caratheodory.le_top m U.compl.toSublocale
      . apply csSup_le
        . simp [Set.Nonempty, W_a, V_a]
          use m.toFun (⊤ : Open E).exterior
          use ⊤
          simp only [and_true]
          exact Sublocale.Open_Neighbourhood.top_mem
        . simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro a wa
          simp [W_a] at wa
          rcases wa with ⟨x, ⟨va, wa⟩⟩
          let h4 := h3 x va
          rw [wa] at h4
          exact le_tsub_of_add_le_right h4


    have h_aux : m.toFun (sSup W_a) = m.toFun U := by
      repeat rw [Measure.caratheodory.open_eq_toFun] at sSup_W_a_eq_U

      exact sSup_W_a_eq_U
    rw [h_aux] at h4
    exact h4
    -- m v_a ≤ m (compl U)
    -- dann sSup machen


  . have h (ε : Real) (hε : ε > 0) : m.toFun ⊤ ≤ m.toFun U + m.caratheodory (U.compl) + ε:= by
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

      have h1 : ∃ W ∈ Sublocale.Open_Neighbourhood U.compl, m.toFun W < m.caratheodory U.compl + ε := by
        rw [Measure.caratheodory]
        have h_nonempty : (m.toFun '' Sublocale.Open_Neighbourhood U.compl.toSublocale).Nonempty := by
          simp only [Set.Nonempty, Set.mem_image]
          use m.toFun ⊤
          use ⊤
          simp only [and_true]
          exact Sublocale.Open_Neighbourhood.top_mem

        let h := h_aux' ε hε (m.toFun '' Sublocale.Open_Neighbourhood U.compl.toSublocale) h_nonempty
        rcases h with ⟨V, h⟩
        simp at h
        rcases h with ⟨⟨x, ⟨h1, h2⟩⟩, h3⟩
        use x
        simp only [h1, true_and]
        rw [h2]
        exact h3
      rcases h1 with ⟨W, ⟨h1, h2⟩⟩
      have h : ↑(m.toFun U) + m.toFun W ≤ ↑(m.toFun U) + ↑(m.caratheodory U.compl.toSublocale) + ε := by
        let h3 := le_of_lt h2
        apply_fun (fun (x : Real) ↦ ↑(m.toFun U) + x) at h3
        dsimp at h3
        apply le_trans h3
        rw [add_assoc]
        simp only [Monotone, add_le_add_iff_left, imp_self, implies_true]

      apply le_trans' h
      have h3 : ↑(m.toFun U) + ↑(m.toFun W) - ↑(m.toFun (U ⊓ W)) ≤ ↑(m.toFun U) + ↑(m.toFun W) := by
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      apply le_trans' h3
      rw [← @strictly_additive]
      refine m.mono ⊤ (U ⊔ W) ?_
      simp only [Sublocale.Open_Neighbourhood, Set.mem_setOf_eq] at h1
      refine Open.le_iff.mpr ?_
      rw [Open.preserves_sup]
      have h4 : U.toSublocale ⊔ U.compl.toSublocale ≤ U.toSublocale ⊔ W.toSublocale := by
        exact sup_le_sup_left h1 U.toSublocale
      apply le_trans' h4
      rw [Open.sup_compl_eq_top]
      apply OrderTop.le_top

    have h1 : m.toFun ⊤ - (m.toFun U + m.caratheodory (U.compl)) ≤ sInf {ε : Real | ε > 0} := by
      apply le_csInf
      rw [Set.Nonempty]
      use 42
      norm_num
      simp only [Set.mem_setOf_eq]
      intro b1 h1
      rw [tsub_le_iff_left]
      exact h b1 h1

    simp_rw [sInf_epsilon_eq_zero] at h1
    simp only [tsub_le_iff_right, zero_add] at h1
    apply h1

noncomputable def Measure.restrict (m : @Measure E e_frm) (w : Open E) : Open E → NNReal :=
  fun x ↦ m.toFun (x ⊓ w)

omit e_regular in
lemma Measure.restrict_mono : ∀ (U V : Open E), U ≤ V → m.restrict w U ≤ m.restrict w V := by
  intro u v h
  simp [Measure.restrict]
  apply Measure.mono
  exact inf_le_inf_right w h

omit e_regular in
lemma Measure.restrict_pseudosymm : ∀ {U V : Open E}, m.restrict w (U ⊔ V) = m.restrict w U + m.restrict w V - m.restrict w (U ⊓ V) := by
  intro u v
  simp [Measure.restrict]
  have h : u ⊓ v ⊓ w = (u ⊓ w) ⊓ (v ⊓ w) := by
    exact inf_inf_distrib_right u v w
  rw [h]
  rw [← Measure.strictly_additive]

  have h : (u ⊔ v) ⊓ w = u ⊓ w ⊔  v ⊓ w := by
    apply_fun (fun x ↦ Open.toSublocale x)
    simp [Open.preserves_inf, Open.preserves_sup]
    exact inf_sup_right u.toSublocale v.toSublocale w.toSublocale
    exact Open.toSublocale_injective
  rw [h]

omit e_regular in
lemma Measure.restrict_filtered : ∀ (s : Set (Open E)), increasingly_filtered s → m.restrict w (sSup s) = sSup (m.restrict w '' s) := by
  intro s h
  simp [Measure.restrict]
  rw [Open.inf_def]
  rw [Open.sSup_def]

  --
  rw [sSup_inf_eq]
  have h_help :  ⨆ a ∈ Open.element '' s, a ⊓ w.element = sSup (Set.range (fun (a : Open.element '' s) ↦ a.val ⊓ w.element)) := by
    simp [sSup_range]
    apply le_antisymm
    . simp only [le_iSup_iff, Subtype.forall, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, iSup_le_iff, imp_self, implies_true]
    . simp only [le_iSup_iff, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂, Subtype.forall,
      Set.mem_image, forall_exists_index, imp_self, implies_true]

  rw [h_help]
  have Open.sSup_eq''  {U_i : Set (E)} : (sSup (Open.mk '' U_i)) = ⟨sSup (U_i)⟩  := by
    rw [Open.sSup_def]
    simp [Set.image_image]
  rw [← Open.sSup_eq'']
  rw [Measure.filtered]
  simp [Set.image_image]

  . have sSup_mono : ∀ a b : Set (NNReal), a = b → sSup a = sSup b := by
      exact fun a b a_1 => congrArg sSup a_1
    apply sSup_mono
    ext x
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_prop, exists_exists_and_eq_and]
    exact Eq.to_iff rfl
  . simp only [increasingly_filtered, Set.mem_image, Set.mem_range, Subtype.exists, exists_prop,
    exists_exists_and_eq_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a1 h1 a2 h2
    rw [increasingly_filtered] at h
    rcases h a1 h1 a2 h2 with ⟨a3, ⟨ha3, ⟨h1, h2⟩⟩⟩
    use a3
    use ha3
    simp_rw [← Open.inf_def]
    apply And.intro
    . exact inf_le_inf_right w h1
    . exact inf_le_inf_right w h2


noncomputable def Measure.restrict_measure  (m : @Measure E e_frm) (w : Open E)  : @Measure E e_frm where
  toFun := Measure.restrict m w
  empty := (by simp[Measure.restrict];exact m.empty)
  mono := restrict_mono
  strictly_additive (U V) := restrict_pseudosymm
  filtered := Measure.restrict_filtered





def Open_Interiors  (u : Sublocale E) := {w : Open E | w ≤ u}
/--
leroy Lemme 4
-/
lemma Measure.add_complement_inf (u : Open E) (a : Sublocale E) : m.caratheodory a = m.caratheodory (a ⊓ u) + m.caratheodory (a ⊓ u.compl) := by
  apply le_antisymm
  .
    have h : a = (a ⊓ u) ⊔ (a ⊓ u.compl.toSublocale) := by
      rw [← @inf_sup_left]
      rw [@Open.sup_compl_eq_top]
      simp only [le_top, inf_of_le_left]
    apply_fun m.caratheodory at h
    apply le_trans' (Measure.caratheodory.subadditive _ _)
    rw [← h]
  .
    have h : ∀ w ∈ Sublocale.Open_Neighbourhood a, (m.restrict_measure w).toFun ⊤  = (m.restrict_measure w).toFun (u) + (m.restrict_measure w).caratheodory (u.compl) := by
      intro w h
      exact Eq.symm (add_complement u)
    simp [Measure.restrict_measure,Measure.restrict] at h

    have h1 :  ∀ w ∈ Sublocale.Open_Neighbourhood a, m.caratheodory (a ⊓ u) + m.caratheodory (a ⊓ u.compl) ≤  m.toFun (u ⊓ w) + (m.restrict_measure w).caratheodory u.compl.toSublocale  := by
        intro w h
        simp [Sublocale.Open_Neighbourhood] at h
        apply add_le_add
        . apply_fun (fun x ↦ x ⊓ u.toSublocale) at h
          apply_fun (fun x ↦ m.caratheodory x) at h
          dsimp at h
          apply le_trans h

          rw [← @Open.preserves_inf]
          rw [Measure.caratheodory.open_eq_toFun]
          rw [inf_comm]
          --
          apply Measure.caratheodory.monotonic
          --
          simp [Monotone]
          exact fun a a_1 a_2 => inf_le_of_left_le a_2
        . simp [Measure.caratheodory, Measure.restrict_measure,Measure.restrict]
          rw [csInf_le_iff]
          simp [lowerBounds]
          intro b h1
          simp [Sublocale.Open_Neighbourhood] at h1
          apply le_csInf
          . simp only [Set.image_nonempty]
            rw [Set.Nonempty]
            use ⊤
            exact Sublocale.Open_Neighbourhood.top_mem
          . simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
            intro a1 h2
            simp [Sublocale.Open_Neighbourhood] at h2
            have h_aux : a ⊓ u.compl.toSublocale ≤ (a1 ⊓ w).toSublocale := by
              rw [inf_comm]
              rw [Open.preserves_inf]
              exact inf_le_inf h2 h

            let h3 := h1 (a1 ⊓ w) h_aux
            exact h3
          . simp only [OrderBot.bddBelow]
          . simp only [Set.image_nonempty, Sublocale.Open_Neighbourhood.Nonempty]
    conv =>
      enter [2]
      rw [Measure.caratheodory]

    apply le_csInf
    . simp
      exact Sublocale.Open_Neighbourhood.Nonempty a
    . intro b h3
      simp at h3
      rcases h3 with ⟨w, ⟨h3, h4⟩⟩
      let h := h w h3
      let h1 := h1 w h3
      rw [← h4]
      rw [h]
      apply h1

/--
Leroy Corollary 1 -/
lemma Measure.restrict_subadditive {U V : Open E} {A : Sublocale E} : m.caratheodory (A ⊓ (U ⊔ V)) = m.caratheodory (A ⊓ U) + m.caratheodory (A ⊓ V) - m.caratheodory (A ⊓ U ⊓ V) := by
  have h : m.caratheodory (A ⊓ (U ⊔ V).toSublocale) = m.caratheodory A - m.caratheodory (A ⊓ (U ⊔ V).compl) := by
      apply eq_tsub_of_add_eq
      rw [← Measure.add_complement_inf]
  rw [compl_sup_eq_inf_compl] at h
  rw [Closed.preserves_inf] at h


  have h2 : m.caratheodory A = m.caratheodory (A ⊓ U ⊓ V) + m.caratheodory (A ⊓ U ⊓ V.compl) + m.caratheodory (A ⊓ U.compl ⊓ V) + m.caratheodory (A ⊓ U.compl ⊓ V.compl) := by
    rw [Measure.add_complement_inf U A]
    rw [Measure.add_complement_inf V (A ⊓ U)]
    rw [Measure.add_complement_inf V (A ⊓ U.compl)]
    ring

  rw [h2] at h
  have h_help : ∀ x, x +  m.caratheodory (A ⊓ U.compl.toSublocale ⊓ V.compl.toSublocale) -
    m.caratheodory (A ⊓ (U.compl.toSublocale ⊓ V.compl.toSublocale)) = x := by
    intro x
    rw [inf_assoc]
    simp only [add_tsub_cancel_right]
  rw [h_help ] at h
  rw [← Measure.add_complement_inf] at h

  have h_help2 : ∀ x, x = x + m.caratheodory (A ⊓ U ⊓ V) - m.caratheodory (A ⊓ U ⊓ V) := by
    exact fun x =>
      Eq.symm (add_tsub_cancel_right x (caratheodory (A ⊓ U.toSublocale ⊓ V.toSublocale)))

  rw [h_help2 (caratheodory (A ⊓ U.toSublocale) + caratheodory (A ⊓ U.compl.toSublocale ⊓ V.toSublocale))] at h
  rw [Open.preserves_sup] at h
  rw [h]
  have h_help3 : m.caratheodory (A ⊓ U.compl.toSublocale ⊓ V.toSublocale) +
      m.caratheodory (A ⊓ U.toSublocale ⊓ V.toSublocale) = m.caratheodory (A ⊓ V) := by
      conv =>
        enter [1, 1, 1]
        rw [inf_assoc]
        rw [inf_comm U.compl.toSublocale]
        rw [← inf_assoc]
      conv =>
        enter [1, 2, 1]
        rw [inf_assoc]
        rw [inf_comm U.toSublocale]
        rw [← inf_assoc]
      rw [add_comm]
      rw [← Measure.add_complement_inf]


  rw [add_assoc]
  rw [h_help3]

omit e_regular in
lemma le_iSup_mem  (s : Set (Open E)) (a : NNReal) (f : Open E → NNReal) :
        (∀ b ∈ s, f b ≤ a) → ⨆ b ∈ s, f b ≤ a := by
      intro h
      apply ciSup_le
      intro b
      by_cases hC : b ∈ s
      . apply @ciSup_le _ _ _ (by simp [hC])
        intro hb
        exact h b hC
      . have h_empty : IsEmpty (b ∈ s) := by exact { false := hC }
        rw [@NNReal.iSup_empty]
        exact zero_le a

omit e_regular in
lemma iSup_mem_eq (s : Set (Open E)) (f : Open E → NNReal) (h_top : ∀ a, f a ≤ f ⊤) : ⨆ b ∈ s, f b = sSup (Set.range (fun b : s => f b.val)) := by
  rw [sSup_range]
  apply_fun ENNReal.ofNNReal
  repeat rw [ENNReal.coe_iSup]
  have h (a : Open E) :  BddAbove (Set.range fun (h : a ∈ s) => f a) := by
    simp [BddAbove, upperBounds, Set.Nonempty]
    use f ⊤
    exact fun a_1 => h_top a

  conv =>
    enter [1, 1, a]
    rw [ENNReal.coe_iSup (h a)]
  rw [iSup_subtype']
  . simp [BddAbove, upperBounds, Set.Nonempty]
    use  f ⊤
    exact fun a a_1 => h_top a
  . simp [BddAbove, upperBounds, Set.Nonempty]
    use f ⊤
    exact fun a => ciSup_le' fun i => h_top a
  . exact ENNReal.coe_injective
/--
Leroy Lemme5
-/
lemma Measure.inf_filtered (A : Sublocale E) (s : Set (Open E)) (h : increasingly_filtered s) :
    m.caratheodory (A ⊓ (sSup s).toSublocale) = ⨆ b ∈ s, m.caratheodory (A ⊓ b) := by
  apply le_antisymm
  .
    have h1 : ∀ ε > 0, m.caratheodory (A ⊓ (sSup s).toSublocale) ≤ (⨆ b ∈ s, m.caratheodory (A ⊓ b.toSublocale)) + ε := by
      intro ε h_ε
      let h2 := @Exists_Neighbourhood_epsilon _ _ m A ε h_ε
      rcases h2 with ⟨W, ⟨h2, h3⟩⟩
      have h4 : ∀ v ∈ s, m.caratheodory (W ⊓ v) ≤ m.caratheodory (A ⊓ v) + ε := by
        intro v hv
        ---
        let lem_4_a := m.add_complement_inf v A
        let lem_4_w := m.add_complement_inf v W
        rw [Measure.caratheodory.open_eq_toFun] at lem_4_w
        ---
        let h3' := h3
        rw [lem_4_a, lem_4_w] at h3'
        have h_help : m.caratheodory (W.toSublocale ⊓ v.compl.toSublocale)
          ≤ m.caratheodory (A ⊓ v.toSublocale) + m.caratheodory (A ⊓ v.compl.toSublocale) + ε := by
          rw [← Measure.add_complement_inf]
          have h' : m.caratheodory (W.toSublocale ⊓ v.compl.toSublocale)  ≤
            m.caratheodory W.toSublocale := by
            apply Measure.caratheodory.monotonic
            exact inf_le_left
          apply le_trans h'
          rw [Measure.caratheodory.open_eq_toFun]
          exact h3
        let h4 := (tsub_le_tsub_iff_right h_help).mpr h3'
        simp only [add_tsub_cancel_right] at h4
        apply le_trans h4
        simp only [tsub_le_iff_right]
        rw [add_assoc _ ε]
        rw [add_assoc]
        apply add_le_add
        . rfl
        . rw [add_comm]
          simp only [add_le_add_iff_left]
          apply Measure.caratheodory.monotonic
          simp only [le_inf_iff, inf_le_right, and_true]
          apply inf_le_of_left_le
          exact h2

      have h5 : m.caratheodory (A ⊓ (sSup s).toSublocale) ≤ m.caratheodory (W ⊓ (sSup s).toSublocale) := by
        apply Measure.caratheodory.monotonic
        exact inf_le_inf h2 (by rfl)
      have h6 : m.caratheodory (W ⊓ (sSup s).toSublocale) = ⨆ b ∈ s, m.caratheodory (W ⊓ b) := by
        conv =>
          enter [2, 1, b, 1]
          rw [← Open.preserves_inf]
          rw [Measure.caratheodory.open_eq_toFun]

        have h_help :  ⨆ b ∈ s, m.toFun (W ⊓ b) = sSup (m.toFun '' (Set.range (fun b : s ↦ W ⊓ b.val))) := by
          rw [iSup_mem_eq]
          . congr
            ext x
            simp only [Set.mem_range, Subtype.exists, exists_prop, Set.mem_image,
              exists_exists_and_eq_and]
          . intro a
            apply m.mono
            refine inf_le_inf (by rfl) (by exact OrderTop.le_top a)

        rw [h_help]
        rw [← m.filtered]
        rw [← Open.preserves_inf]
        rw [Measure.caratheodory.open_eq_toFun]
        congr
        repeat rw [Open.inf_def, Open.sSup_def]
        ext
        simp only
        rw [inf_sSup_eq]
        . simp only [Set.mem_image, iSup_exists, Open.inf_def, Open.sSup_def]
          rw [← Set.range_comp, Function.comp_def]
          simp only
          rw [sSup_range]
          --- v geht safe schöner (vlt doch nicht)
          apply le_antisymm <;> simp only [le_iSup_iff, Subtype.forall, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂,
            imp_self, implies_true]
        . simp only [increasingly_filtered, Set.mem_range, Subtype.exists, exists_prop,
          exists_exists_and_eq_and, le_inf_iff, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, inf_le_left, true_and]
          intro a ha a1 ha1
          simp [increasingly_filtered] at h
          let h' := h a ha a1 ha1
          rcases h' with ⟨a2,⟨ha2, ⟨h', h''⟩ ⟩⟩
          use a2
          use ha2
          refine ⟨inf_le_of_right_le h', inf_le_of_right_le h''⟩

      apply le_trans h5
      rw [h6]
      apply le_iSup_mem
      intro b hb

      -- vlt gehts schöner
      rw [iSup_mem_eq, sSup_range]

      have h_help (a b : NNReal) : a ≤ b ↔ (a : ℝ) ≤ (b : ℝ) := by
        exact ge_iff_le
      apply (h_help _ _).mpr
      rw [NNReal.coe_add, NNReal.coe_iSup]
      have h_nonempty : Nonempty ↑s := by
        use b
      rw [ciSup_add]
      . norm_cast
        let h4' := h4 b hb
        apply le_trans h4'
        rw [le_ciSup_iff']
        . simp only [Subtype.forall]
          intro b1 h
          exact h b hb
        . simp [BddAbove, upperBounds, Set.Nonempty]
          use m.caratheodory ⊤ + ε
          intro a ha
          simp only [add_le_add_iff_right]
          apply Measure.caratheodory.le_top
      . simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_range, Subtype.exists, exists_prop,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
        use m.caratheodory ⊤
        norm_cast
        intro a ha
        apply Measure.caratheodory.le_top
      . intro a
        apply Measure.caratheodory.monotonic
        exact inf_le_inf (by rfl) (by simp only [Open.top_toSublocale, le_top])


    have h7 : ∀ ε > 0, m.caratheodory (A ⊓ (sSup s).toSublocale) - ⨆ b ∈ s, m.caratheodory (A ⊓ b.toSublocale) ≤ ε := by
      intro e he
      let h8 := h1 e he
      rw [tsub_le_iff_left]
      exact h8

    rw [← add_zero (⨆ i ∈ s, caratheodory (A ⊓ i.toSublocale))]
    rw [← sInf_epsilon_eq_zero']
    rw [← tsub_le_iff_left]
    apply le_csInf
    . simp only [Set.Nonempty, gt_iff_lt, Set.mem_setOf_eq]
      use 42
      norm_num
    exact h7
  .
    apply le_iSup_mem

    intro b
    intro hb
    apply Measure.caratheodory.monotonic
    apply inf_le_inf
    . rfl
    . rw [Open.preserves_sSup]
      apply le_sSup
      exact Set.mem_image_of_mem Open.toSublocale hb
def Image (A : Sublocale E) := {x : E // A x = x}
instance (A : Sublocale E)  : Order.Frame (Image A) := sorry

def Measure.restrict_sublocale (m : @Measure E _) (A : Sublocale E) : Open (Image A) → NNReal :=
  fun x ↦ m.toFun ⟨x.element.val⟩


def Measure.restrict_sublocale_measure (m : @Measure E _) (A : Sublocale E) : @Measure (Image A) _ where
  toFun := Measure.restrict_sublocale m A
  empty := sorry
  mono := sorry
  strictly_additive := sorry
  filtered := sorry
