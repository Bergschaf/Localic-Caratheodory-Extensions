import Leroy.Measure.Basic

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]


def well_inside (U V : Open E) := U.closure ≤ V.toSublocale

infix:100 " ≪ " => well_inside

/--
Stone spaces s.80
und auch Sketches of an Elephant 501...
-/
def well_inside_iff (U V : Open E) : U ≪ V ↔ ∃ c, c ⊓ U = ⊥ ∧ c ⊔ V = ⊤ := by
  rw [well_inside]

  sorry

/--
Leroy definition
TODO Stone spaces als quelle anschauen
Steht auch in Sketches of an Elephant 501
da steht covered -> Muss da U ≤ sSup ... stehen?
-/
def regular (E : Type*)  [Order.Frame E]: Prop :=
  ∀ (U : Open E), U = sSup {V : Open E | V ≪ U}


variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]

variable {m : @Measure E e_frm}(X_n : ℕ → Sublocale E)

def E_to_Open (x : E) : Open E := ⟨x⟩

/--
TODO dass muss weiter nach vorne
-/
lemma E_le_iff (x y : E) : x ≤ y ↔ E_to_Open x ≤ E_to_Open y := by
  repeat rw [E_to_Open]
  apply Iff.intro
  . intro h
    exact Open.le_iff.mpr h
  . intro h
    exact eckig_preserves_inclusion.mpr h

@[simp]
lemma E_to_Open_Open (x : Open E) : E_to_Open ↑x = x := by rfl

/--
Leroy Lemme 2.2
TODO stone spaces als quelle vlt
Seite 81. 1.2
Maybe depends on:
Nucleus.eq_join_open_closed
-/

lemma sublocal_intersection_of_neighbours {a : Sublocale E} : a = sInf (Neighbourhood a) := by
  apply le_antisymm
  . apply le_sInf
    exact fun b a_1 => le_Neighbourhood b a_1
  suffices h : (∀ H, a H = ⨆ V ∈ Neighbourhood a, V H) by
    sorry
  intro H
  let K := a H
  let V (W : Open E) := W.closure.compl ⊔ ⟨H⟩

  have h (W : Open E) (h : W.closure ≤ (↑K : Open E).toSublocale) :
    W ≤ E_to_Open ((V W).toSublocale H) := by
    have h_V : V W ∈ Open_Neighbourhood a := by sorry

    have h : W ⊓ V W = W ⊓ (⟨H⟩ : Open E) := by sorry
    have h1 : W ⊓ ⟨H⟩ ≤ ⟨H⟩ := by sorry
    sorry


  have h1 : E_to_Open (a H) = sSup {W : Open E | W.closure ≤ (⟨a H⟩ : Open E).toSublocale} := by
    sorry


  apply_fun E_to_Open
  rw [h1]
  sorry
  sorry
/--
Leroy Lemme 3
-/
lemma Measure.add_complement (U : Open E) : m.toFun U + m.caratheodory (U.compl) = m.toFun (⊤ : Open E) := by

  apply le_antisymm
  .
    let V_a := Open_Neighbourhood (complement U)
    let W_a := Open.exterior '' V_a
    have sSup_W_a_eq_U : sSup W_a = U := by
      rw [e_regular.elim U]
      apply le_antisymm
      . simp only [sSup_le_iff]
        intro b h
        apply le_sSup
        simp [Set.mem_setOf_eq, well_inside]
        simp [W_a] at h
        rcases h with ⟨a, ⟨h1, h2⟩⟩
        rw [← h2]
        simp only [V_a] at h1
        simp only [Open_Neighbourhood, Set.mem_setOf_eq] at h1
        rw [closure_eq_compl_exterior_compl]
        rw [Open.exterior_exterior_eq_self]
        apply le_compl_iff.mp
        exact h1
      . simp only [well_inside, Open_Neighbourhood, sSup_le_iff, Set.mem_setOf_eq, W_a, V_a]
        intro b h

        apply le_sSup
        simp only [Set.mem_image, Set.mem_setOf_eq]
        use b.exterior
        apply And.intro
        . apply compl_le_iff.mpr
          exact h
        . exact Open.exterior_exterior_eq_self b

    apply_fun m.caratheodory at sSup_W_a_eq_U
    have W_a_filtered_croissant : increasingly_filtered W_a := by
      rw [increasingly_filtered]
      intro u hu v hv
      use u ⊔ v
      apply And.intro
      . simp only [Open_Neighbourhood, Set.mem_image, Set.mem_setOf_eq, W_a, V_a]
        simp [W_a,V_a] at hu hv
        rcases hu with ⟨u1, ⟨hu1, hu2⟩⟩
        rcases hv with ⟨v1, ⟨hv1, hv2⟩⟩
        use (u1 ⊓ v1)
        apply And.intro
        . let x := Open_Neighbourhood.inf_closed u1 hu1 v1 hv1
          simp_rw [Open_Neighbourhood] at x
          simp at x
          exact x
        . rw [← hu2,← hv2]
          exact Open.exterior_inf_eq_sup
      . apply And.intro
        . exact Open.le_sup_left u v
        . exact Open.le_sup_right u v

    have h1 : ∀ v_a ∈ V_a, m.toFun (v_a.exterior) + m.toFun v_a ≤ m.caratheodory ⊤ := by
      intro v_a h_v_a
      have h : m.toFun v_a.exterior + m.toFun v_a = m.toFun v_a.exterior + m.toFun v_a - m.toFun (v_a.exterior ⊓ v_a) := by
        have h1 :  m.toFun (v_a.exterior ⊓ v_a) = 0 := by
          rw [inf_comm]
          rw [@inf_Exterior_eq_bot]
          exact m.empty
        conv =>
          enter [1]
          rw [← tsub_zero (m.toFun v_a.exterior + m.toFun v_a)]
          rw [← h1]
      rw [h]
      rw [← @pseudosymm]
      have h1 : v_a.exterior ⊔ v_a ≤ ⊤ := by
        simp only [le_top]
      apply_fun m.toFun at h1
      rw [caratheodory_top]
      exact h1
      apply Measure.mono

    have h2 : ∀ v_a ∈ V_a, m.caratheodory (U.compl) ≤ m.toFun v_a := by
      intro va hva
      simp [V_a, Open_Neighbourhood] at hva
      rw [Open.complement_eq]
      apply_fun m.caratheodory at hva
      rw [Caratheodory_opens] at hva
      exact hva
      apply Caratheodory_monotonic
    rw [Measure.caratheodory_top] at h1
    have h3 : ∀ v_a ∈ V_a, m.toFun v_a.exterior + m.caratheodory (U.compl) ≤ m.toFun ⊤ := by
      intro va hva
      exact add_le_of_add_le_left (h1 va hva) (h2 va hva)

    have h4 : m.toFun (sSup W_a) + m.caratheodory (U.compl) ≤ m.toFun ⊤ := by
      rw [m.filtered _ W_a_filtered_croissant]
      apply add_le_of_le_tsub_right_of_le
      . rw [← Measure.caratheodory_top]
        exact Caratheodory.le_top m U.compl.toSublocale
      . apply csSup_le
        . simp [Set.Nonempty, W_a, V_a]
          use m.toFun (⊤ : Open E).exterior
          use ⊤
          simp only [and_true]
          exact Open_Neighbourhood.top_mem
        . simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          intro a wa
          simp [W_a] at wa
          rcases wa with ⟨x, ⟨va, wa⟩⟩
          let h4 := h3 x va
          rw [wa] at h4
          exact le_tsub_of_add_le_right h4


    have h_aux : m.toFun (sSup W_a) = m.toFun U := by
      repeat rw [Caratheodory_opens] at sSup_W_a_eq_U
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

      have h1 : ∃ W ∈ Open_Neighbourhood U.compl, m.toFun W < m.caratheodory U.compl + ε := by
        rw [Measure.caratheodory]
        have h_nonempty : (m.toFun '' Open_Neighbourhood U.compl.toSublocale).Nonempty := by
          simp only [Set.Nonempty, Set.mem_image]
          use m.toFun ⊤
          use ⊤
          simp only [and_true]
          exact Open_Neighbourhood.top_mem

        let h := h_aux' ε hε (m.toFun '' Open_Neighbourhood U.compl.toSublocale) h_nonempty
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
      rw [← @pseudosymm]
      refine m.mono ⊤ (U ⊔ W) ?_
      simp only [Open_Neighbourhood, Set.mem_setOf_eq] at h1
      refine Open.le_iff_sublocale.mpr ?_
      rw [Open.Max_eq]
      have h4 : U.toSublocale ⊔ U.compl.toSublocale ≤ U.toSublocale ⊔ W.toSublocale := by
        exact sup_le_sup_left h1 U.toSublocale
      apply le_trans' h4
      rw [Open.complement_eq]
      rw [sup_comp_eq_top]
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
  rw [← Measure.pseudosymm]

  have h : (u ⊔ v) ⊓ w = u ⊓ w ⊔  v ⊓ w := by
    apply_fun (fun x ↦ Open.toSublocale x)
    simp [Open.Min_eq, Open.Max_eq]
    exact inf_sup_right u.toSublocale v.toSublocale w.toSublocale
    exact Open.toSublocale_injective
  rw [h]

lemma Measure.restrict_filtered : ∀ (s : Set (Open E)), increasingly_filtered s → m.restrict w (sSup s) = sSup (m.restrict w '' s) := by
  intro s h
  simp [Measure.restrict]
  simp_rw [Open_min]
  simp_rw [Open_sSup]
  --
  rw [sSup_inf_eq]
  rw [iSup]
  rw [← Open.sSup_eq'']
  rw [Measure.filtered]
  simp [Set.image_image]
  . iSup const

  . sorry










noncomputable def Measure.restrict_measure  (m : @Measure E e_frm) (w : Open E)  : @Measure E e_frm where
  toFun := Measure.restrict m w
  empty := (by simp[Measure.restrict];exact m.empty)
  mono := restrict_mono
  pseudosymm := restrict_pseudosymm
  filtered := sorry






def Open_Interiors  (u : Sublocale E) := {w : Open E | w ≤ u}
/--
leroy Lemme 4
-/
lemma Measure.add_complement_inf (u : Open E) (a : Sublocale E) : m.caratheodory a = m.caratheodory (a ⊓ u) + m.caratheodory (a ⊓ u.compl) := by
  apply le_antisymm
  .
    have h : a = (a ⊓ u) ⊔ (a ⊓ u.compl.toSublocale) := by
      rw [← @inf_sup_left]
      rw [@Open.sup_compl]
      simp only [le_top, inf_of_le_left]
    apply_fun m.caratheodory at h
    apply le_trans' (Caratheodory_subadditive _ _)
    rw [← h]
  .
    have h : ∀ w ∈ Open_Neighbourhood a, (m.restrict_measure w).toFun ⊤  = (m.restrict_measure w).toFun (u) + (m.restrict_measure w).caratheodory (u.compl) := by
      intro w h
      exact Eq.symm (add_complement u)
    simp [Measure.restrict_measure,Measure.restrict] at h

    have h1 :  ∀ w ∈ Open_Neighbourhood a, m.caratheodory (a ⊓ u) + m.caratheodory (a ⊓ u.compl) ≤  m.toFun (u ⊓ w) + (m.restrict_measure w).caratheodory u.compl.toSublocale  := by
        intro w h
        simp [Open_Neighbourhood] at h
        apply add_le_add
        . apply_fun (fun x ↦ x ⊓ u.toSublocale) at h
          apply_fun (fun x ↦ m.caratheodory x) at h
          dsimp at h
          apply le_trans h
          rw [← @Open.Min_eq]
          rw [@Caratheodory_opens]
          rw [inf_comm]
          --
          apply Caratheodory_monotonic
          --
          simp [Monotone]
          exact fun a a_1 a_2 => inf_le_of_left_le a_2
        . simp [Measure.caratheodory, Measure.restrict_measure,Measure.restrict]
          rw [csInf_le_iff]
          simp [lowerBounds]
          intro b h1
          simp [Open_Neighbourhood] at h1
          apply le_csInf
          . simp only [Set.image_nonempty]
            rw [Set.Nonempty]
            use ⊤
            exact Open_Neighbourhood.top_mem
          . simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
            intro a1 h2
            simp [Open_Neighbourhood] at h2
            have h_aux : a ⊓ u.compl.toSublocale ≤ (a1 ⊓ w).toSublocale := by
              rw [inf_comm]
              rw [Open.Min_eq]
              exact inf_le_inf h2 h

            let h3 := h1 (a1 ⊓ w) h_aux
            exact h3
          . simp only [OrderBot.bddBelow]
          . simp only [Set.image_nonempty, Open_Neighbourhood.Nonempty]
    conv =>
      enter [2]
      rw [Measure.caratheodory]

    apply le_csInf
    . simp only [Set.image_nonempty, Open_Neighbourhood.Nonempty]
    . intro b h3
      simp at h3
      rcases h3 with ⟨w, ⟨h3, h4⟩⟩
      let h := h w h3
      let h1 := h1 w h3
      rw [← h4]
      rw [h]
      apply h1

omit e_regular in
lemma todo_name {U V : Open E} : (U ⊔ V).compl = U.compl ⊓ V.compl := by
  apply_fun ((fun x ↦ ↑x) : Closed E → Sublocale E)
  simp [Open.compl,Closed.toSublocale, complement]
  ext x
  simp
  rw [Closed.Min_eq']
  simp [Open.Max_eq']
  --
  exact injective_of_le_imp_le (fun (x : Closed E) => x.toSublocale) fun {x y} a => a

/--
Leroy Corollary 1 -/
lemma Measure.restrict_subadditive {U V : Open E} {A : Sublocale E} : m.caratheodory (A ⊓ (U ⊔ V)) = m.caratheodory (A ⊓ U) + m.caratheodory (A ⊓ V) - m.caratheodory (A ⊓ U ⊓ V) := by
  have h : m.caratheodory (A ⊓ (U ⊔ V).toSublocale) = m.caratheodory A - m.caratheodory (A ⊓ (U ⊔ V).compl) := by
      apply eq_tsub_of_add_eq
      rw [← Measure.add_complement_inf]
  rw [todo_name] at h
  rw [Closed.Min_eq] at h


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
  rw [Open.Max_eq] at h
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

/--
Leroy Lemme5
-/
lemma Measure.inf_filtered (A : Sublocale E) (s : Set (Open E)) (h : increasingly_filtered s) :
    m.caratheodory (A ⊓ (sSup s).toSublocale) = ⨆ b ∈ s, m.caratheodory (A ⊓ b) := by
  sorry



def Image (A : Sublocale E) := {x : E // A x = x}
instance (A : Sublocale E)  : Order.Frame (Image A) := sorry

def Measure.restrict_sublocale (m : @Measure E _) (A : Sublocale E) :Open (Image A) → NNReal :=
  fun x ↦ m.toFun ⟨x.element.val⟩


def Measure.restrict_sublocale_measure (m : @Measure E _) (A : Sublocale E) : @Measure (Image A) _ where
  toFun := Measure.restrict_sublocale m A
  empty := sorry
  mono := sorry
  pseudosymm := sorry
  filtered := sorry
