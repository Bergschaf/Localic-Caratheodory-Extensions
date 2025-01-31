import Leroy.Measure.Regular

variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]
variable {E' : Type*} [Order.Frame E']

--variable {m : @Measure E' _}
variable {m : @Measure E _}


-- TODO Infrastruktur, dass man Sublocals als Local ansehen kann

def e_μ (m : @Measure E' _) (u : E') : E' := (sSup {w : Open E' | w ≤ u ∧ m.toFun w = m.toFun u}).element

lemma e_μ_idempotent (m : @Measure E' _) : ∀ (x : E'), e_μ m (e_μ m x) ≤ e_μ m x := by
  simp [e_μ, ← Open.le_iff]
  intro x a h1 h2
  apply le_sSup
  simp
  simp [Open.le_iff] at h1
  rw [← Open.le_iff] at h1
  apply And.intro
  . apply le_trans h1
    simp only [sSup_le_iff, Set.mem_setOf_eq, and_imp]
    intro a b c
    exact Open.le_iff.mpr b
  . rw [h2]
    apply Measure.monotone
    ext
    simp
    rw [← Open.ext_iff]
    simp only [le_antisymm_iff, sSup_le_iff, Set.mem_setOf_eq, and_imp, le_refl, and_self, le_sSup,
      and_true]
    exact fun b a a_1 a_2 => a


lemma e_μ_le_apply (m : @Measure E' _) : ∀ (x : E'), x ≤ e_μ m x := by
  intro x
  simp [e_μ]
  rw [← Open.le_iff]
  apply le_sSup
  simp

lemma e_μ_map_inf (m : @Measure E' _) : ∀ (x y : E'), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y
  sorry

def μ_Reduction (m : @Measure E' _): Nucleus E' where
  toFun := e_μ m
  idempotent' x := e_μ_idempotent m x
  le_apply' x := e_μ_le_apply m x
  map_inf' x y:= e_μ_map_inf m x y




def decroissante (V : Set (Open E')) : Prop :=
  ∀ v ∈ V, ∃ u ∈ V, u ≤ v

def decroissante' (V : ℕ → Open E) : Prop :=
  ∀ n : ℕ, V (n+1) ≤ V n

def filtrante_decroissante (V : ℕ → Sublocale E) : Prop :=
  ∀ n m : ℕ, ∃ l, V l ≤ V n ∧ V l ≤ V m

/--
Leroy lemma 6
-/
lemma leroy_6 (V_n : ℕ → (Open E)) (h : decroissante' V_n) :
    m.caratheodory (iInf (Open.toSublocale ∘ V_n)) = iInf (m.toFun ∘ V_n) := by
  let I :=  (iInf (Open.toSublocale ∘ V_n))

  let F_n (n : ℕ) := Closed.toSublocale (Open.compl (V_n n))
  let G := iSup (F_n)

  have h : G ⊔ I = ⊤ := by
    simp [G, I, F_n, iSup,iInf]
    rw [@sup_sInf_eq]
    simp [iInf]
    apply eq_top_iff.mpr
    simp
    intro a
    apply eq_top_iff.mpr
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
    rw [Open.sup_compl]

  apply le_antisymm
  . simp [iInf]
    apply le_csInf
    . exact Set.range_nonempty (m.toFun ∘ V_n)
    simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff, I,
      F_n, G]
    intro n
    rw [← Caratheodory_opens]
    apply Caratheodory_monotonic
    apply sInf_le
    simp only [Set.mem_range, Function.comp_apply, exists_apply_eq_apply, I, F_n, G]

  have h1 : m.caratheodory ⊤ ≤ m.caratheodory I + m.caratheodory G := by
    rw [← h]
    rw [sup_comm]
    exact Caratheodory_subadditive I G

  have h1_ : m.caratheodory ⊤ - m.caratheodory G ≤ m.caratheodory I := by
    exact
      (OrderedSub.tsub_le_iff_right (Measure.caratheodory ⊤) (Measure.caratheodory G)
            (Measure.caratheodory I)).mpr
        h1

  have h2 : m.caratheodory G = iSup (m.caratheodory ∘ F_n) := by
    apply le_antisymm
    . simp [iSup]
      sorry

    . simp [iSup]
      apply csSup_le
      . exact Set.range_nonempty (Measure.caratheodory ∘ F_n)
      simp
      intro n
      apply Caratheodory_monotonic
      apply le_sSup
      simp only [Set.mem_range, exists_apply_eq_apply, I, F_n, G]

  have h3 : ⨅ n : ℕ, (m.toFun ⊤ - m.caratheodory (F_n n)) ≤ m.caratheodory I := by
    apply le_trans' h1_
    have h_help (a : NNReal) (s : ℕ → (NNReal)) : ⨅ n, a - s n = a - iSup s := by
      sorry

    rw [h_help]
    rw [← Caratheodory_opens]
    simp only [Open.top_sublocale]
    apply tsub_le_tsub
    . rfl
    . sorry

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
lemma leroy_7 (A_i : ℕ → Sublocale E) (h : filtrante_decroissante A_i) :
  m.caratheodory (iInf A_i) = iInf (m.caratheodory ∘ A_i) := by

  let V_n (n : ℕ) := Open_Neighbourhood (A_i n)
  admit -- TODO noha fragen
