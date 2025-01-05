import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Sublocales
import Leroy.Further_Topology

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]



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


lemma Open_Neighbourhood.inf_closed {x : Sublocale E} : ∀ U ∈ Open_Neighbourhood x, ∀ V ∈ Open_Neighbourhood x, U ⊓ V ∈ Open_Neighbourhood x := by
  sorry

/--
Leroy Lemme 1
Wie kriegt er V_n, also voisinages die weniger als εₙ größer sind als X_n
-> Magie

lemma preserves_sup (m : @Measure X h) (X_n : Set (Sublocale X)) (h : increasing X_n) : m.caratheodory (sSup X_n) = sSup (m.caratheodory '' X_n) := by
  simp [Measure.caratheodory]
  have h_epsilon : ∃ r : NNReal, r > 0 := by
    use 1
    exact Real.zero_lt_one
  let ε := Classical.choose h_epsilon
  have h_epsilon' : ε > 0 := by
    simp [ε]
    apply Classical.choose_spec
  have h_epsilon_n :  ∃ (e_n : ℕ → NNReal),∀ n : ℕ,( ∑ i ∈ Finset.range n, e_n i < ε) ∧ 0 < e_n n := by
    let d (n : ℕ) := (0.5 * ε) / (2 ^ n)
    use d
    intro n
    simp [d]
    sorry
  let e_n := Classical.choose h_epsilon_n
  have h_e_n : ∀ n : ℕ, 0 < e_n n := by
    intro n
    simp [e_n]
    let x := Classical.choose_spec h_epsilon_n n
    exact x.right


  have h_1 : ∀ x_n ∈ X_n, ∃ neighbour ∈ Open_Neighbourhood (x_n), m.toFun neighbour - m.caratheodory (x_n) < ε / n :=  by
    intro n
    simp [Measure.caratheodory]
    -- TODO noa fragen
    --- ggf sInf kommutiert mit measure
    sorry


  let V_n (n : ℕ) := Classical.choose (h_1 n)

  let W_n (n : ℕ) := iSup (fun (x : Fin n) ↦ V_n x)

  let W := iSup (W_n)

  have h_2 : W = iSup (V_n) := by
    simp [W, W_n]
    sorry

  have h_3 : ∀ n : ℕ, m.toFun (W_n n) - m.caratheodory (X_n n) ≤ ∑ i ∈ Finset.range (n), e_n i := by sorry

  have h_4 : m.toFun (W) ≤ ε + iSup (fun n ↦ (m.caratheodory (X_n n))) := by sorry


  have h_trivial : ∀ n : ℕ, iSup (m.caratheodory ∘ X_n) ≤ m.caratheodory (iSup X_n) := by
    intro n

    apply ciSup_le
    intro x
    simp [Measure.caratheodory]
    apply csInf_le_csInf'
    simp
    let x := Open_Neighbourhood_nonempty (iSup  X_n)
    --apply @Set.nonempty_of_nonempty_subtype _ _
    --
    sorry -- sieht schlecht auss
    sorry

  sorry
-/


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

/--
Leroy Lemme 2.2
TODO stone spaces als quelle vlt
Seite 81. 1.2
Maybe depends on:
Nucleus.eq_join_open_closed
-/
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




/--
Leroy Lemme 3
-/
lemma Measure.add_complement {m : @Measure E e_frm} {U : Open E} : m.toFun U + m.caratheodory (U.compl) = m.toFun (⊤ : Open E) := by

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

    have h_aux : sInf {ε : Real | ε > 0} = 0 := by
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
    simp [h_aux] at h1
    exact h1
