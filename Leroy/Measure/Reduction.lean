import Leroy.Measure.Regular

variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]
variable {E' : Type*} [Order.Frame E']

--variable {m : @Measure E' _}
variable {m : @Measure E _}


-- TODO Infrastruktur, dass man Sublocals als Local ansehen kann

def e_μ (m : @Measure E' _) (u : E') : E' := (sSup {w : Open E' | w ≤ u ∧ m.toFun w = m.toFun ⟨u⟩}).element

lemma e_μ_idempotent (m : @Measure E' _) : ∀ (x : E'), e_μ m (e_μ m x) ≤ e_μ m x := by
  simp [e_μ, ← Open.le_iff, Open.le_def, Open.sSup_def]
  intro x a h1 h2 h3 h4
  apply le_sSup
  simp
  use h1
  simp [h4]
  sorry

lemma e_μ_le_apply (m : @Measure E' _) : ∀ (x : E'), x ≤ e_μ m x := by
  intro x
  simp [e_μ]
  sorry

lemma e_μ_map_inf (m : @Measure E' _) : ∀ (x y : E'), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y
  apply le_antisymm
  . sorry
  . sorry

def μ_Reduction (m : @Measure E' _): Nucleus E' where
  toFun := e_μ m
  idempotent' x := e_μ_idempotent m x
  le_apply' x := e_μ_le_apply m x
  map_inf' x y:= e_μ_map_inf m x y


variable {ι : Type*} [PartialOrder ι] [Nonempty ι]


def decroissante' (V : ι → Open E) : Prop :=
  ∀ i j : ι, i ≤ j → V j ≤ V i

def decroissante (V : Set (Open E')) : Prop :=
  decroissante' (fun (x : V) ↦ x.val)



def filtrante_decroissante (V : ι → Sublocale E) : Prop :=
  ∀ n m : ι, ∃ l, V l ≤ V n ∧ V l ≤ V m



/--
Leroy Lemma 6
-/
lemma Measure.caratheodory.preserves_sInf (V_n : ℕ → (Open E)) (h : decroissante' V_n) :
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
        have h : increasing (Set.range F_n) := by
          simp [increasing, F_n]
          intro a
          use a + 1
          simp [decroissante'] at h
          rw [← Closed.le_iff]
          rw [Closed.le_def]
          simp
          exact h _ _ (Nat.le_add_right _ _)
        rw [sSup_range]
        rw [preserves_sup]
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
lemma leroy_7 (A_i : ι → Sublocale E) (h : filtrante_decroissante A_i) :
  m.caratheodory (iInf A_i) = iInf (m.caratheodory ∘ A_i) := by

  let V_n (n : ι) := Sublocale.Open_Neighbourhood (A_i n)
  admit -- TODO noha fragen
