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

/--
Leroy Lemme 1
Wie kriegt er V_n, also voisinages die weniger als εₙ größer sind als X_n
-> Magie
-/
lemma preserves_sup (m : @Measure X h) (X_n : Finset (Sublocale X)) (h : increasing X_n.toSet) (h_nonempty : X_n.Nonempty): m.caratheodory (sSup X_n) = sSup (m.caratheodory '' X_n) := by
  simp [Measure.caratheodory]
  have h_epsilon : ∃ r : NNReal, r > 0 := by
    use 1
    exact Real.zero_lt_one
  let ε := Classical.choose h_epsilon
  have h_epsilon' : ε > 0 := by
    simp [ε]
    apply Classical.choose_spec

  have h_1 : ∀ x_n ∈ X_n, ∃ neighbour ∈ Open_Neighbourhood (x_n), m.toFun neighbour - m.caratheodory (x_n) ≤ ε / X_n.card :=  by
    intro n h
    rw [Measure.caratheodory]
    let m_real := NNReal.toReal ∘ m.toFun
    let h1 := @Real.lt_sInf_add_pos (m_real '' Open_Neighbourhood n) (by simp[Set.Nonempty];use m_real ⊤;use ⊤;apply And.intro; exact Open_Neighbourhood.top_mem; simp only [Function.comp_apply,m_real])
    have h_pos :  0 < ε / X_n.card := by
      rw [propext (div_pos_iff_of_pos_left h_epsilon')]
      rw [@Nat.cast_pos]
      rw [Finset.card_pos]
      exact h_nonempty

    let h1 := @h1 (ε / X_n.card) (by exact h_pos)
    simp at h1
    rcases h1 with ⟨a, ⟨h1, h2⟩⟩
    use a
    apply And.intro
    . exact h1
    . apply_fun (fun x ↦ x -sInf (m_real '' Open_Neighbourhood n)) at h2
      simp at h2
      simp [m_real] at h2

      let h2 := le_of_lt h2
      apply le_trans' h2
      simp only [NNReal.val_eq_coe]

      sorry
      simp only [StrictMono, sub_lt_sub_iff_right, imp_self, implies_true]
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
  rw [← Caratheodory_opens]
  simp_rw [Open.Min_eq]
  rw [Open.sSup_eq]






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
lemma Measure.add_complement_inf {u : Open E} {a : Sublocale E} : m.caratheodory a = m.caratheodory (a ⊓ u) + m.caratheodory (a ⊓ u.compl) := by
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
