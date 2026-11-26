/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Leroy.Measure.Regular
public import Leroy.Measure.Restrict

/-!
# Measure reduction sublocales

For a measure `m` on a frame `E`, this file (port of the "reduction" chapter of
Leroy's thesis) constructs the measure-induced reduction `e_μ m`, exhibits it as a
nucleus, and studies its sublocale `μ_Reduction m` — the smallest sublocale on which
the Caratheodory measure of `m` is unchanged.  It then proves Leroy's Lemma 6 and
Lemme 7 (the Caratheodory measure sends decreasingly filtered infima of sublocales
to infima) and establishes strict additivity of the Caratheodory measure on
sublocales.
-/

@[expose] public section

open Sublocale

section
variable {E : Type*} [Order.Frame E] {m : @Measure E _}

/-- For a measure `m` on a frame `E` and an element `u : E`, `e_μ m u` is the supremum
of all opens `w` lying above `u` whose measure agrees with the measure of `u`; read
as an element of `E`, it is the reduction of `u` determined by `m`. -/
def e_μ (m : @Measure E _) (u : E) : E :=
  (sSup {w : Open E | u ≤ w ∧ m.toFun w = m.toFun ⟨u⟩}).element

/-- Reduction preserves measure values: the measure of the reduced element `e_μ m u`
equals the measure of `u` itself. -/
lemma e_μ_Measure_eq (m : @Measure E _) (u : E) : m.toFun ⟨e_μ m u⟩ = m.toFun ⟨u⟩ := by
  simp only [e_μ, Open.sSup_def]
  rw [← Open.sSup_def]
  rw [Measure.filtered]
  · apply le_antisymm
    · rw [csSup_le_iff]
      · simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
        intro b x h1 h2 h3
        rw [← h3, h2]
      · simp only [BddAbove, Set.Nonempty, upperBounds, Set.mem_image, Set.mem_ofPred_eq,
          forall_exists_index, and_imp]
        use m.toFun ⊤
        intro a x h1 h2 h3
        rw [← h3]
        exact Measure.all_le_top x
      · simp only [Set.Nonempty, Set.mem_image, Set.mem_ofPred_eq, ↓existsAndEq, and_true]
        use ⟨u⟩
    · rw [le_csSup_iff]
      · simp only [upperBounds, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
        intro b h
        exact h ⟨u⟩ (by rfl) (by rfl) (by rfl)
      · simp only [
          BddAbove,
          Set.Nonempty,
          upperBounds,
          Set.mem_image,
          Set.mem_ofPred_eq,
          forall_exists_index,
          and_imp]
        use m.toFun ⟨u⟩
        intro a x h1 h2 h3
        rw [← h3, h2]
      --
      · simp only [Set.Nonempty, Set.mem_image, Set.mem_ofPred_eq, ↓existsAndEq, and_true]
        use ⟨u⟩
  · rw [increasingly_filtered]
    simp_all only [Set.mem_ofPred_eq, and_imp]
    intro a h1 h2 b h3 h4
    use a ⊔ b
    · simp only [Open.sup_def]
      apply And.intro
      · apply And.intro
        · apply le_trans h1 le_sup_left
        · apply le_antisymm
          · rw [← Open.sup_def]
            rw [Measure.strictly_additive]
            rw [h2, h4]
            have h5 : m.toFun ⟨u⟩ ≤ m.toFun (a ⊓ b) := by
              apply Measure.mono
              change u ≤ (a ⊓ b).element
              rw [Open.inf_def]
              exact le_inf h1 h3
            exact tsub_le_iff_right.mpr (by nlinarith [h5])
          · apply Measure.mono
            simp only [Open.le_def]
            apply le_trans h1 le_sup_left
      · apply And.intro
        · simp [Open.le_def]
        · simp [Open.le_def]


/-- The reduction `e_μ m` is idempotent: applying it twice does not enlarge the result.
This idempotence is one of the nucleus laws needed for `e_μ_nucleus`. -/
lemma e_μ_idempotent (m : @Measure E _) : ∀ (x : E), e_μ m (e_μ m x) ≤ e_μ m x := by
  intro x
  simp only [e_μ, Open.sSup_def, sSup_le_iff, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index,
    and_imp]
  intro a b c d e
  subst e
  --
  apply le_sSup
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  use b
  simp only [and_true]
  apply And.intro
  · apply c
    on_goal 3 => {rfl
    }
    · simp_all only [le_refl]
    · simp_all only
  rw [d]
  let h := @e_μ_Measure_eq E _ m x
  simp only [e_μ, Open.mk_element] at h
  exact h


/-- The reduction `e_μ m` is inflationary: every element `x` of the frame is bounded
by its reduction `e_μ m x`. -/
lemma e_μ_le_apply (m : @Measure E _) : ∀ (x : E), x ≤ e_μ m x := by
  intro x
  simp only [e_μ, Open.sSup_def]
  apply le_sSup
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  use ⟨x⟩

/-- The reduction `e_μ m` is monotone: if `x ≤ y` in the frame, then
`e_μ m x ≤ e_μ m y`. -/
lemma e_μ_mono (m : @Measure E _) (x y : E) : x ≤ y → e_μ m x ≤ e_μ m y := by
  intro h
  conv =>
    enter [2]
    simp [e_μ]
  simp only [Open.sSup_def, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_ofPred_eq,
    forall_exists_index, and_imp]
  intro c h3
  let h4 := @h3 (y ⊔ (e_μ m x)) ⟨(y ⊔ (e_μ m x))⟩
  apply le_trans (@le_sup_left  _ _ _ y)
  rw [sup_comm]
  apply h4
  · simp
  · rw [← Open.sup_def]
    rw [Measure.strictly_additive]
    rw [e_μ_Measure_eq]
    have h5 : m.toFun ({ element := y } ⊓ { element := e_μ m x }) = m.toFun ⟨x⟩ := by
      apply le_antisymm
      · rw [Measure.strictly_additive']
        rw [← e_μ_Measure_eq m x]
        simp only [tsub_le_iff_right]
        rw [add_comm]
        simp only [add_le_add_iff_left]
        apply Measure.mono
        · simp
      · apply Measure.mono
        simp only [le_inf_iff]
        apply And.intro
        · exact h
        · apply e_μ_le_apply
    rw [h5]
    simp
  · simp


/-- The reduction `e_μ m` preserves binary infima: reducing `x ⊓ y` gives the infimum
of the reductions of `x` and `y`.  This infimum-preservation is the defining property
turning `e_μ m` into a nucleus. -/
lemma e_μ_map_inf (m : @Measure E _) : ∀ (x y : E), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y
  apply le_antisymm
  · refine le_inf_iff.mpr ?_
    apply And.intro
    · apply e_μ_mono
      simp
    · apply e_μ_mono
      simp
  · simp only [e_μ, Open.sSup_def]
    rw [sSup_inf_sSup]
    simp only [Set.mem_prod, Set.mem_image, Set.mem_ofPred_eq, le_sSup_iff, upperBounds,
      forall_exists_index, and_imp, iSup_le_iff, Prod.forall]
    intro a h1 b c d h2 h3 h4 e h5 h6 h7
    subst h4 h7
    let h1' := @h1 (d ⊓ e) ⟨d ⊓ e⟩
    simp only [le_inf_iff, forall_const, and_imp] at h1'
    apply h1'
    · exact inf_le_of_left_le h2
    · exact inf_le_of_right_le h5
    · rw [← Open.inf_def]
      apply le_antisymm
      · rw [← Open.inf_def]
        repeat rw [Measure.strictly_additive']
        rw [h3, h6]
        repeat rw [NNReal.sub_def]
        have hsup : m.toFun ({ element := x } ⊔ { element := y }) ≤
            m.toFun (d ⊔ e) := by
          apply Measure.mono
          simp only [Open.sup_def, Open.le_def]
          exact sup_le_sup h2 h5
        have hsup' : (m.toFun ({ element := x } ⊔ { element := y }) : Real) ≤
            (m.toFun (d ⊔ e) : Real) := by exact_mod_cast hsup
        exact Real.toNNReal_mono (by nlinarith [hsup'])
      · apply Measure.mono
        simp only [Open.inf_def, Open.le_def]
        exact inf_le_inf h2 h5


/-- The measure reduction `e_μ m`, bundled as a nucleus on the frame `E`: the maps
`e_μ m` are inflationary, idempotent, and preserve binary infima. -/
def e_μ_nucleus (m : @Measure E _) : Nucleus E where
  toFun := e_μ m
  map_inf' := e_μ_map_inf m
  idempotent' := e_μ_idempotent m
  le_apply' := e_μ_le_apply m

/-- The measure reduction sublocale: the sublocale of `E` induced by the nucleus
`e_μ_nucleus m`, i.e. the smallest sublocale on which the measure of `m` keeps the
same values. -/
def μ_Reduction (m : @Measure E _) : Sublocale E :=
  (e_μ_nucleus m).toSublocale

/-- Applying the reduction sublocale to an element unfolds to the reduction function
`e_μ m`. -/
@[simp] lemma μ_Reduction_apply (m : @Measure E _) (x : E) :
    μ_Reduction m x = e_μ m x := by
  simp [μ_Reduction, e_μ_nucleus]


/-- If applying the sublocale `U` to each element preserves the measure values,
i.e. `m ⟨U i⟩ = m ⟨i⟩` for every `i`, then `U` contains the reduction: the measure
reduction is the least sublocale with this property. -/
lemma Measure.μ_Reduction_le_if (m : @Measure E _) (U : Sublocale E) :
    (∀ i, m.toFun ⟨U i⟩ = m.toFun ⟨i⟩) → μ_Reduction m ≤ U := by
  intro h
  apply (Sublocale.le_iff (μ_Reduction m) U).2
  intro i
  rw [μ_Reduction_apply]
  change U i ≤ (sSup {w : Open E | i ≤ w.element ∧ m.toFun w = m.toFun ⟨i⟩}).element
  rw [Open.sSup_def]
  apply le_sSup
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨⟨U i⟩, ⟨U.le_apply i, h i⟩, rfl⟩


/-- Every open (element of the open neighbourhood filter) of the reduction sublocale
has full measure: `m.toFun V = m.toFun ⊤`. -/
lemma Measure_Neighbourhood_μ_eq_top (m : @Measure E _) :
    ∀ V ∈ openNhds (μ_Reduction m), m.toFun V = m.toFun ⊤ := by
  intro V h
  have h : ∀ W : E, V.toSublocale W ≤ μ_Reduction m W := by
    simpa [openNhds, Sublocale.le_iff] using h
  have hV := h V.element
  have htop : ⊤ ≤ e_μ m V.element := by
    simpa only [Open.toSublocale_apply, himp_self, μ_Reduction_apply] using hV
  have heq : e_μ m V.element = ⊤ := top_unique htop
  calc
    m.toFun V = m.toFun ⟨V.element⟩ := rfl
    _ = m.toFun ⟨e_μ m V.element⟩ := (e_μ_Measure_eq m V.element).symm
    _ = m.toFun ⊤ := by rw [heq, ← Open.top_element]

/-- Reduction removes no mass: the Caratheodory measure of the reduction sublocale
`μ_Reduction m` equals the total measure `m.toFun ⊤`. -/
lemma Measure_μ_Reduction_eq_top (m : @Measure E _) :
    m.caratheodory (μ_Reduction m) = m.toFun ⊤ := by
  apply le_antisymm
  · apply Measure.caratheodory.le_top_toFun
  simp only [Measure.caratheodory]
  apply le_csInf
  · use m.toFun ⊤
    use ⊤
    simp only [and_true]
    exact openNhds_top_mem
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a h
  apply le_of_eq (Measure_Neighbourhood_μ_eq_top m a h).symm

/-- Under the regularity hypothesis, the reduction sublocale is the infimum of the
sublocales of all full-measure opens `w`, i.e. those with `m.toFun w = m.toFun ⊤`. -/
lemma μ_Reduction_eq_sInf [Fact (regular E)] (m : @Measure E _) :
    μ_Reduction m = sInf (Open.toSublocale '' {w : Open E | m.toFun w = m.toFun ⊤}) := by
  rw [Sublocale.intersection_Open_Neighbourhhood (μ_Reduction _)]
  apply le_antisymm
  · simp only [le_sInf_iff, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro a h
    --
    apply sInf_le
    simp only [Set.mem_image]
    use a
    simp only [openNhds, Set.mem_ofPred_eq, and_true]
    ---
    have h1 : ∀ H : Open E, m.toFun (a ⊓ H) = m.toFun H := by
      intro H
      have h2 : m.toFun (a ⊓ H) = m.toFun a + m.toFun H - m.toFun (a ⊔ H) := by
        exact Measure.strictly_additive' a H
      rw [h2]
      have h3 : m.toFun (a ⊔ H) = m.toFun ⊤ := by
        apply le_antisymm
        · exact Measure.all_le_top (a ⊔ H)
        · have h1 : m.toFun (a) ≤ m.toFun (a ⊔ H) := by
            apply Measure.mono
            simp
          apply le_trans' h1
          rw [← h]
      simp [h, h3]
    ----- UUUUU sehr wichtig (ähnlich wie bei lemma 7)
    change μ_Reduction m ≤ a.toSublocale
    rw [Sublocale.le_iff]
    intro i
    let h2 := h1 ⟨a.element ⇨ i⟩
    simp [Open.inf_def] at h2
    let h3 := h1 ⟨i⟩
    simp only [Open.inf_def] at h3
    rw [Open.toSublocale_apply, μ_Reduction_apply]
    rw [e_μ, Open.sSup_def]
    apply le_sSup
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    refine ⟨⟨a.element ⇨ i⟩, ?_, rfl⟩
    exact ⟨le_himp_iff.mpr inf_le_left, h2.symm.trans h3⟩
  · simp only [le_sInf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    apply sInf_le
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    use a
    simp only [and_true]
    exact Measure_Neighbourhood_μ_eq_top m a h

/-- Under the regularity hypothesis, the reduction sublocale is the infimum of all
sublocales `w` with full Caratheodory measure `m.caratheodory w = m.toFun ⊤`. -/
lemma μ_Reduction_eq_sInf_Sublocale [Fact (regular E)] (m : @Measure E _) :
    μ_Reduction m = sInf ({w : Sublocale E | m.caratheodory w = m.toFun ⊤}) := by
  apply le_antisymm
  · rw [μ_Reduction_eq_sInf]
    simp only [le_sInf_iff, Set.mem_ofPred_eq]
    intro a h
    rw [csInf_le_iff]
    · simp only [lowerBounds, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro b h1
      rw [Sublocale.intersection_Open_Neighbourhhood a]
      simp only [
                 openNhds,
                 le_sInf_iff,
                 Set.mem_image,
                 Set.mem_ofPred_eq,
                 forall_exists_index,
                 and_imp,
                 forall_apply_eq_imp_iff₂]
      intro c h2
      apply h1
      apply le_antisymm
      · exact Measure.all_le_top c
      · rw [← h]
        rw [← Measure.caratheodory.open_eq_toFun]
        apply Measure.caratheodory.mono
        exact h2
    · exact OrderBot.bddBelow (Open.toSublocale '' {w | m.toFun w = m.toFun ⊤})
    · use ⊤
      simp_all only [Set.mem_image, Set.mem_ofPred_eq]
      apply Exists.intro
      · apply And.intro
        · rfl
        · simp_all only [Open.top_toSublocale]
  · apply csInf_le
    · exact OrderBot.bddBelow {w | Measure.caratheodory w = m.toFun ⊤}
    · simp only [Set.mem_ofPred_eq]
      apply Measure_μ_Reduction_eq_top


/-- The reduction sublocale is dominated by every sublocale `A` of full Caratheodory
measure: `μ_Reduction m` is the greatest lower bound of the full-measure sublocales. -/
lemma μ_Reduction_le_of_top [Fact (regular E)] (m : @Measure E _) (A : Sublocale E)
    (h : m.caratheodory A = m.toFun ⊤) :
    μ_Reduction m ≤ A := by
  rw [μ_Reduction_eq_sInf_Sublocale]
  apply sInf_le
  · simp [h]



variable [Fact (regular E)]
/-- For an open `b` of the image of a sublocale `A`, the Caratheodory measure of the
embedded open `A.embed b` equals the value of the restricted measure on `b`. -/
lemma embed_measure_open (A : Sublocale E) (b : Open (Image A.toNucleus)) :
    m.caratheodory (A.embed b) = (m.restrict_sublocale_measure A).toFun b := by
  simp [Measure.restrict_sublocale_measure,Measure.restrict_sublocale]


/-- Embedding a sublocale `b` of the image of `A` back into `E` transports the
Caratheodory measure: it agrees with the Caratheodory measure of the measure
restricted to `A`, evaluated at `b`. -/
lemma embed_measure (A : Sublocale E) (b : Sublocale (Image A.toNucleus)) :
    m.caratheodory (A.embed b) = (m.restrict_sublocale_measure A).caratheodory b := by
  apply le_antisymm
  · simp only [Measure.caratheodory, Measure.restrict_sublocale_measure, Measure.restrict_sublocale]
    apply le_csInf
    · simp
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    apply le_csInf
    · simp
    · simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro c h1
      simp only [openNhds, Set.mem_ofPred_eq] at h h1
      rw [csInf_le_iff]
      · simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq]
        intro d h2
        simp only [openNhds, Set.mem_ofPred_eq] at h2
        apply h2
        apply le_trans' h1
        apply_fun A.embed at h
        · exact h
        exact embed.mono A
      · use 0
        simp [lowerBounds]
      · simp
  · simp only [Measure.caratheodory, Measure.restrict_sublocale_measure, Measure.restrict_sublocale]
    apply le_csInf
    · simp
    · simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a h
      rw [csInf_le_iff]
      · simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq]
        intro c h1
        ---- Man braucht die restriction für offene
        have h2 : A.restrict_open a ∈ b.openNhds := by
          simp only [openNhds, Set.mem_ofPred_eq] at h ⊢
          apply_fun (· ⊓ A) at h
          · simp only at h
            have h_help : A.embed b ⊓ A = A.embed b := by
              apply le_antisymm
              · simp
              · simp only [le_inf_iff, le_refl, true_and]
                exact embed_le A b
            rw [h_help] at h
            have h1 := A.restrict_mono _ _ (by simp) (by exact embed_le A b) h
            rw [Sublocale.restrict_embed] at h1
            apply le_trans h1
            rw [Sublocale.restrict_open_eq_restrict]
            apply Sublocale.restrict_mono
            simp
          · rw [Monotone]
            exact fun ⦃a b⦄ a_1 => inf_le_inf_right A a_1
        have h3 := h1 (A.restrict_open a) h2
        --
        apply le_trans h3
        rw [Measure.restrict_sublocale]
        rw [← Measure.caratheodory.open_eq_toFun]
        apply Measure.caratheodory.mono
        rw [embed_restrict_open]
        simp
      · use 0
        simp [lowerBounds]
      · simp


/-- Reduction inside the image: the reduction of the measure restricted to `A`,
applied in the image sublocale of `A` and embedded back into `E`. -/
noncomputable def R_μ (A : Sublocale E) : Sublocale E :=
  A.embed (μ_Reduction (m.restrict_sublocale_measure A))

/-- Reduction does not change the Caratheodory measure: `A` and its reduced version
`R_μ A` carry the same Caratheodory measure. -/
lemma μ_R_μ_eq (A : Sublocale E) : m.caratheodory A = m.caratheodory (@R_μ _ _ m _ A) := by
  rw [R_μ]
  rw [embed_measure]
  rw [Measure_μ_Reduction_eq_top]
  rw [← Measure.caratheodory.open_eq_toFun]
  rw [← embed_measure]
  rw [Open.top_toSublocale]
  rw [embed_top]

end

variable {ι : Type*} [PartialOrder ι] [Nonempty ι]
variable {E : Type*} [Order.Frame E] [Fact (regular E)] {m : @Measure E _}

/--
Leroy Lemma 6
-/
lemma Measure.preserves_iInf (V_n : ℕ → (Open E)) (h : Antitone V_n) :
    m.caratheodory (iInf (Open.toSublocale ∘ V_n)) = iInf (m.toFun ∘ V_n) := by
  let I :=  (iInf (Open.toSublocale ∘ V_n))
  let F_n (n : ℕ) := Closed.toSublocale (Open.compl (V_n n))
  let G := iSup (F_n)
  have h_ : G ⊔ I = ⊤ := by
    simp only [iSup, iInf, G, F_n, I]
    rw [@sup_sInf_eq]
    simp only [
               iInf,
               sInf_eq_top,
               Set.mem_range,
               forall_exists_index,
               forall_apply_eq_imp_iff,
               Function.comp_apply,
               exists_prop,
               and_imp,
               forall_apply_eq_imp_iff₂]
    intro a
    rw [eq_top_iff]
    simp only [top_le_iff]
    rw [eq_top_iff]
    simp only [top_le_iff]
    apply le_antisymm le_top
    have hcomp : (V_n a).compl.toSublocale ≤ G := by
      exact le_iSup_of_le a le_rfl
    calc
      ⊤ = (V_n a).toSublocale ⊔ (V_n a).compl.toSublocale :=
        (Open.sup_compl_eq_top (V_n a)).symm
      _ ≤ (V_n a).toSublocale ⊔ G := sup_le_sup le_rfl hcomp
      _ = G ⊔ (V_n a).toSublocale := sup_comm _ _
  apply le_antisymm
  · simp only [iInf]
    apply le_csInf
    · exact Set.range_nonempty (m.toFun ∘ V_n)
    simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff]
    intro n
    rw [← Measure.caratheodory.open_eq_toFun]
    apply Measure.caratheodory.mono
    apply sInf_le
    simp only [Set.mem_range, Function.comp_apply, exists_apply_eq_apply]
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
    · simp only [iSup, G]
      rw [le_csSup_iff]
      · simp only [
                   upperBounds,
                   Set.mem_range,
                   Function.comp_apply,
                   forall_exists_index,
                   forall_apply_eq_imp_iff,
                   Set.mem_ofPred_eq]
        intro b h2
        have h : Monotone F_n := by
          simp only [Monotone, F_n]
          intro a b h1
          simp only [Antitone] at h
          rw [← Closed.le_iff]
          rw [Closed.le_def]
          simp only [Open.compl_element, ← Open.le_def]
          exact h h1
        rw [sSup_range]
        rw [Measure.caratheodory.preserves_sup']
        · apply ciSup_le
          exact h2
        exact h
      · simp only [
                   BddAbove,
                   Set.Nonempty,
                   upperBounds,
                   Set.mem_range,
                   Function.comp_apply,
                   forall_exists_index,
                   forall_apply_eq_imp_iff,
                   Set.mem_ofPred_eq]
        use m.caratheodory ⊤
        exact fun a => Measure.caratheodory.le_top m (F_n a)
      · exact Set.range_nonempty (Measure.caratheodory ∘ F_n)
    · simp only [iSup]
      apply csSup_le
      · exact Set.range_nonempty (Measure.caratheodory ∘ F_n)
      simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff]
      intro n
      apply Measure.caratheodory.mono
      apply le_sSup
      simp only [Set.mem_range, exists_apply_eq_apply, F_n]
  have h3 : ⨅ n : ℕ, (m.toFun ⊤ - m.caratheodory (F_n n)) ≤ m.caratheodory I := by
    apply le_trans' h1_
    have h_help (a : NNReal) (f : ℕ → (NNReal)) (hf : BddAbove (Set.range fun i => f i)) :
        a - ⨆ i, f i = ⨅ i, a - f i := by
      apply_fun (ENNReal.ofNNReal)
      · simp only [ENNReal.coe_sub]
        rw [@ENNReal.coe_iInf]
        simp only [ENNReal.coe_sub]
        rw [ENNReal.coe_iSup]
        · refine ENNReal.sub_iSup ?_
          · exact ENNReal.coe_ne_top
        exact hf
      · exact ENNReal.coe_injective
    rw [← h_help]
    · rw [← Measure.caratheodory.open_eq_toFun]
      simp only [Open.top_toSublocale]
      apply tsub_le_tsub
      · rfl
      · rw [h2]
        rfl
    simp only [
               BddAbove,
               Set.Nonempty,
               upperBounds,
               Set.mem_range,
               forall_exists_index,
               forall_apply_eq_imp_iff,
               Set.mem_ofPred_eq]
    use m.caratheodory ⊤
    exact fun a => Measure.caratheodory.le_top m (F_n a)
  have h4 : ⨅ n : ℕ, (m.toFun ⊤ - m.caratheodory (F_n n)) = iInf (m.toFun ∘ V_n)  := by
    simp only [iInf, F_n]
    have h5 : Set.range (fun n => (m.toFun ⊤) - m.caratheodory (V_n n).compl.toSublocale) =
        (Set.range (m.toFun ∘ V_n)) := by
      rw [Set.range_eq_iff]
      simp only [Set.mem_range, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff]
      apply And.intro
      · intro n
        use n
        rw [← Measure.add_complement (V_n n)]
        simp only [add_tsub_cancel_right]
      · intro n
        use n
        rw [← Measure.add_complement (V_n n)]
        simp only [add_tsub_cancel_right]
    rw [h5]
  simp_rw [h4, I] at h3
  exact h3




/-- A concrete characterisation of convergence in `ℝ≥0∞` towards a finite limit
`a`: `f` tends to `a` iff for every strictly positive error `ε ≠ ⊤`, the values of
`f n` eventually lie in the interval `[a - ε, a + ε]`. -/
lemma ENNReal.tendsto_atTop' {β : Type u_2} [Nonempty β] [SemilatticeSup β] {f : β → ENNReal}
    {a : ENNReal} (ha : a ≠ ⊤) :
    Filter.Tendsto f Filter.atTop (nhds a) ↔ ∀ ε > 0, (h : ε ≠ ⊤) →
      ∃ (N : β), ∀ n ≥ N, f n ∈ Set.Icc (a - ε) (a + ε) := by
  apply Iff.intro
  · intro h
    let x := (ENNReal.tendsto_atTop ha).mp h
    intro e he h1
    apply x e he
  · intro h
    have h1 : ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Set.Icc (a - ε) (a + ε) := by
      intro e he
      by_cases hC : e = ⊤
      · subst hC
        simp
      apply h e he hC
    exact (ENNReal.tendsto_atTop ha).mpr h1

/-- The stacked running infima of a sequence of opens: `rec' seq n` is the infimum of
`seq 0, …, seq n`, built recursively as `seq (n + 1) ⊓ rec' seq n`; the resulting
sequence is antitone. -/
def rec' (seq : ℕ → Open E)
  | 0 => seq 0
  | Nat.succ n => seq (n + 1) ⊓ (rec' seq n)

/-- Leroy lemme 7 -/
lemma Measure.caratheodordy.preserves_iInf {ι : Type*} [Nonempty ι] (A_i : ι → Sublocale E)
    (h : decreasingly_filtered A_i) :
  m.caratheodory (iInf A_i) = iInf (m.caratheodory ∘ A_i) := by
  apply le_antisymm
  · simp only [OrderBot.bddBelow, le_ciInf_iff, Function.comp_apply]
    intro i
    apply Measure.caratheodory.mono
    exact iInf_le A_i i
  let V_a := {w : Open E | ∃ i, w ∈ (A_i i).openNhds}
  have h_V_A_inf_closed (u v : Open E) (h1 : u ∈ V_a) (h2 : v ∈ V_a) : u ⊓ v ∈ V_a := by
    simp only [openNhds, Set.mem_ofPred_eq, V_a] at h1 h2 ⊢
    rcases h1 with ⟨i, h1⟩
    rcases h2 with ⟨j, h2⟩
    rcases h i j with ⟨k, ⟨h3, h4⟩⟩
    use k
    simp only [Open.preserves_inf, le_inf_iff]
    apply And.intro
    · apply le_trans h3 h1
    · apply le_trans h4 h2
  have hvn_1 : iInf A_i = sInf (Open.toSublocale '' V_a) := by
    apply le_antisymm
    · simp only [le_sInf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a h
      simp only [Set.mem_ofPred_eq, V_a] at h
      rcases h with ⟨i, h⟩
      simp only [openNhds, Set.mem_ofPred_eq] at h
      exact iInf_le_of_le i h
    simp only [le_iInf_iff]
    intro i
    have h1 : sInf (Open.toSublocale '' V_a) ≤
        sInf (Open.toSublocale '' ((A_i i ).openNhds)) := by
      apply sInf_le_sInf
      refine Set.image_mono ?_
      simp only [V_a]
      refine Set.subset_ofPred.mpr ?_
      exact fun x a => Exists.intro i a
    apply le_trans h1
    rw [← @intersection_Open_Neighbourhhood]
  have V_n_nonempty : Nonempty V_a := by
    use ⊤
    simp only [openNhds, Set.mem_ofPred_eq, Open.top_toSublocale, le_top, exists_const,
      V_a]
  have hvn_2 : ⨅ i, m.caratheodory (A_i i) = ⨅ w : V_a, m.toFun w := by
    apply le_antisymm
    · apply le_ciInf
      intro x
      rcases x with ⟨x, hxV⟩
      change x ∈ V_a at hxV
      rcases hxV with ⟨y, hx⟩
      simp only [openNhds, Set.mem_ofPred_eq] at hx
      refine ciInf_le_of_le ?_ y ?_
      · use 0
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
    · use 42
      simp
    simp only [gt_iff_lt, Set.mem_ofPred_eq, tsub_le_iff_right, V_a]
    intro b hb
    obtain ⟨w, ⟨hw1, hw2⟩⟩ := (@Exists_Neighbourhood_epsilon _ _ m (A_i i) b (by exact hb))
    refine ciInf_le_of_le ?_ ⟨w, (by use i)⟩ ?_
    · use 0
      simp [lowerBounds]
    simp only
    apply le_trans hw2
    rw [add_comm]
  rw [Function.comp_def]
  rw [hvn_2]
  have h_V_a_nonempty : ((m.toFun '' V_a)).Nonempty := by exact Set.Nonempty.of_subtype
  ------------- Wichitig
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_seq_tendsto_sInf (h_V_a_nonempty) (by use 0;simp[lowerBounds])
  -------------
  simp only [Set.mem_image] at hu3
  let V_n' (n : ℕ) := Classical.choose (hu3 n)
  let V_n := rec' (fun n ↦ Classical.choose (hu3 n))
  have V_n_decroissante : Antitone V_n := by
    simp only [Antitone]
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
      simp only [Function.comp_apply, NNReal.coe_inj]
      obtain ⟨_, V_n_spec⟩ :=Classical.choose_spec (hu3 x)
      rw [V_n_spec]
    rw [h_help]
    apply_fun ENNReal.ofNNReal
    · rw [ENNReal.coe_iInf]
      rw [← Function.comp_def]
      rw [@iInf_eq_of_tendsto ℕ ENNReal _ _ _ _ _  (ENNReal.ofNNReal ∘ u) ↑(sInf (m.toFun '' V_a))
        (by
          apply Monotone.comp_antitone
          · simp [Monotone]
          exact hu1)]
      refine (ENNReal.tendsto_atTop' ?_).mpr ?_
      · simp
      · simp only [gt_iff_lt, ge_iff_le, Function.comp_apply, Set.mem_Icc, tsub_le_iff_right]
        intro e he he1
        ----
        rw [@Metric.tendsto_atTop] at hu2
        obtain ⟨n, hn⟩ := hu2 e.toReal (ENNReal.toReal_pos he.ne' he1)
        use n
        intro n1 hn1
        let hn := hn n1 hn1
        rw [NNReal.dist_eq] at hn
        rw [abs_lt] at hn
        simp only [neg_lt_sub_iff_lt_add] at hn
        rcases hn with ⟨hn1 ,hn2⟩
        apply And.intro
        · refine ENNReal.coe_le_iff.mpr ?_
          intro p hp
          refine NNReal.coe_le_coe.mp ?_
          apply le_trans (le_of_lt hn1)
          apply_fun ENNReal.toReal at hp
          simp only [ENNReal.coe_toReal] at hp
          rw [← hp]
          rw [ENNReal.toReal_add]
          · simp only [ENNReal.coe_toReal, add_comm, le_refl]
          · exact ENNReal.coe_ne_top
          · exact he1
        · refine ENNReal.coe_le_iff.mpr ?_
          intro p hp
          refine NNReal.coe_le_coe.mp ?_
          rw [@sub_lt_iff_lt_add'] at hn2
          apply le_trans (le_of_lt hn2)
          apply_fun ENNReal.toReal at hp
          simp only [ENNReal.coe_toReal] at hp
          rw [← hp, ENNReal.toReal_add]
          · simp only [ENNReal.coe_toReal, le_refl, V_a]
          · exact ENNReal.coe_ne_top
          · exact he1
    · exact ENNReal.coe_injective
  have iInf_V_n'_eq_iInf_V_n : iInf (m.toFun ∘ V_n') = iInf (m.toFun ∘ V_n) := by
    apply le_antisymm
    · apply le_ciInf
      intro n
      rw [h_iInf_V_n]
      rw [csInf_le_iff]
      · simp only [lowerBounds, Set.mem_image, forall_exists_index, and_imp, Set.mem_ofPred_eq,
          Function.comp_apply, V_a]
        intro b hb
        obtain ⟨i, hi⟩ : ∃ i, V_n n ∈ (A_i i).openNhds := by
          simp only [V_n]
          induction n with
          | zero =>
            simp only [Set.mem_ofPred_eq, V_a]
            obtain ⟨spec, _⟩ := Classical.choose_spec (hu3 0)
            simp only [Set.mem_ofPred_eq, V_a] at spec
            exact spec
          | succ n hn =>
            simp only [openNhds, Set.mem_ofPred_eq] at hn
            rcases hn with ⟨i,hn⟩
            simp only [
                       openNhds,
                       rec',
                       Set.mem_ofPred_eq,
                       Open.preserves_inf,
                       le_inf_iff,
                       V_a]
            obtain ⟨spec2, _⟩ := Classical.choose_spec (hu3 (n + 1))
            simp only [Set.mem_ofPred_eq, V_a] at spec2
            obtain ⟨j, spec2⟩ := spec2
            obtain ⟨k, hk⟩ := (h i j)
            use k
            simp only [openNhds, Set.mem_ofPred_eq] at spec2
            exact And.intro (le_trans hk.right spec2) (le_trans hk.left hn)
        exact hb (V_n n) i hi rfl
      · use 0
        simp [lowerBounds]
      · simp only [Set.image_nonempty]
        use ⊤
        simp [V_a, Sublocale.openNhds]
    · apply le_ciInf
      intro n
      refine ciInf_le_of_le ?_ n ?_
      · use 0
        simp [lowerBounds]
      · simp only [Function.comp_apply, V_n, V_n', V_a]
        cases n
        · simp [rec']
        · simp only [rec']
          apply Measure.mono
          simp
  rw [sInf_image'] at h_iInf_V_n
  rw [← h_iInf_V_n]
  rw [iInf_V_n'_eq_iInf_V_n]
  rw [hvn_1]
  rw [← Measure.preserves_iInf] -- lemme 6
  · let I := (iInf (Open.toSublocale ∘ V_n))
    have hI : (iInf (Open.toSublocale ∘ V_n)) = I := rfl
    rw [hI]
    ---
    rw [μ_R_μ_eq I]
    apply Measure.caratheodory.mono
    ---
    simp only [le_sInf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    --- ....
    have h2 : m.caratheodory (a ⊓ I) = m.caratheodory I := by
      apply le_antisymm
      · apply Measure.caratheodory.mono
        simp
      rw [← hI]
      rw [inf_iInf]
      simp only [Function.comp_apply]
      conv =>
        enter [2, 1, 1, x]
        rw [← Open.preserves_inf]
      have h_decroissante : Antitone fun x => a ⊓ V_n x := by
          simp only [Antitone, le_inf_iff, inf_le_left, true_and]
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
      simp only [Function.comp_apply]
      rw [Measure.preserves_iInf]
      · rw [← iInf_V_n'_eq_iInf_V_n]
        rw [h_iInf_V_n]
        apply csInf_le
        · apply OrderBot.bddBelow
        · simp only [Set.mem_range, Subtype.exists, exists_prop]
          use a ⊓ V_n n
          simp only [and_true]
          have h_v_n : V_n n ∈ V_a := by
            have spec (n : ℕ):= (Classical.choose_spec (hu3 n)).left
            induction n with
            | zero =>
              simp only [rec', V_n]
              exact spec 0
            | succ n hn =>
              simp_rw [V_n, rec']
              simp only [V_n] at hn
              apply h_V_A_inf_closed
              · exact spec (n + 1)
              · exact hn
          simp only [openNhds, Set.mem_ofPred_eq, V_a] at ha h_v_n ⊢
          rcases ha with ⟨i, ha⟩
          rcases h_v_n with ⟨j, h_v_n⟩
          rw [Open.preserves_inf]
          rw [decreasingly_filtered] at h
          obtain ⟨l, ⟨h1, h2⟩⟩ := h i j
          use l
          apply le_inf
          · apply le_trans h1 ha
          · apply le_trans h2 h_v_n
      · exact V_n_decroissante
    have test := @embed_measure E _ m _ I (I.restrictSublocale (a ⊓ I) (by simp))
    rw [Sublocale.embed_restrict] at test
    have h_help : a.toSublocale ⊓ I ≤ a := by simp
    apply le_trans' h_help
    apply Sublocale.restrict_orderiso I _ _ (by
      rw [R_μ]; exact embed_le I (μ_Reduction (restrict_sublocale_measure I m))) (by simp)
    simp_rw [R_μ]
    rw [Sublocale.restrict_embed]
    have h : Fact (regular (Image I.toNucleus)) := by
      refine { out := ?_ }
      exact Image_regular' I
    apply μ_Reduction_le_of_top
    rw [← test]
    rw [h2]
    simp only [restrict_sublocale_measure, restrict_sublocale, Open.top_toSublocale]
    rw [embed_top]
  · exact V_n_decroissante

/-- The Caratheodory measure on sublocales is strictly additive: the measure of a
binary sup `A ⊔ B` equals the sum of the measures of `A` and `B`, minus the measure
of their intersection `A ⊓ B`. -/
theorem Measure.caratheodory.strictly_additive (A B : Sublocale E) :
    m.caratheodory (A ⊔ B) = m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B) := by
  have h_n_1 : Nonempty ↑A.openNhds := nonempty_openNhds A
  have h_n_2 : Nonempty ↑B.openNhds := nonempty_openNhds B
  have h_n_3 : Nonempty ↑(A ⊔ B).openNhds := nonempty_openNhds (A ⊔ B)
  have h_n_4 : Nonempty ↑(A ⊓ B).openNhds := nonempty_openNhds (A ⊓ B)
  have h_n_5 : Nonempty ↑(A ⊓ B).nhds := nonempty_nhds (A ⊓ B)
  have h1 : m.caratheodory (A ⊔ B) =
      ⨅ v_a : openNhds A, ⨅ w_b : openNhds B, m.toFun (v_a ⊔ w_b) := by
    apply le_antisymm
    · simp only [OrderBot.bddBelow, le_ciInf_iff, Subtype.forall]
      intro a ha b hb
      rw [← Measure.caratheodory.open_eq_toFun]
      apply Measure.caratheodory.mono
      rw [Open.preserves_sup]
      exact sup_le_sup ha hb
    · simp only [caratheodory]
      rw [sInf_image']
      simp only [OrderBot.bddBelow, le_ciInf_iff, Subtype.forall]
      intro a ha
      --
      refine ciInf_le_of_le ?_ ⟨a, (by
        simp only [openNhds, Set.mem_ofPred_eq]
        apply le_trans' ha
        exact le_sup_left)⟩ ?_
      · use 0
        simp only [lowerBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq, zero_le, implies_true]
      refine ciInf_le_of_le ?_ ⟨a, (by
        simp only [openNhds, Set.mem_ofPred_eq]
        apply le_trans' ha
        exact le_sup_right)⟩ ?_
      · use 0
        simp only [lowerBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, Set.mem_ofPred_eq, zero_le, implies_true]
      apply Measure.mono
      simp only [le_refl, sup_of_le_left]
  have h2 : m.caratheodory (A ⊓ B) =
      ⨅ v_a : openNhds A, ⨅ w_b : openNhds B, m.toFun (v_a ⊓ w_b) := by
    apply_fun ENNReal.ofNNReal
    · rw [ENNReal.coe_iInf]
      conv =>
        enter [2, 1, a]
        rw [ENNReal.coe_iInf]
      rw [iInf_prod']
      · rw [← ENNReal.coe_iInf]
        simp only [ENNReal.coe_inj]
        rw [Sublocale.intersection_Neighbourhood A]
        rw [Sublocale.intersection_Neighbourhood B]
        repeat rw [sInf_eq_iInf]
        repeat rw [iInf_subtype']
        have h_n : Nonempty (Subtype (Membership.mem A.nhds)) := by
          exact nonempty_nhds A
        have h_n' : Nonempty (Subtype (Membership.mem B.nhds)) := by
          exact nonempty_nhds B
        rw [iInf_inf]
        conv =>
          enter [1, 1, 1, x]
          rw [inf_iInf]
        rw [iInf_prod']
        rw [Measure.caratheodordy.preserves_iInf]
        · rw [Function.comp_def]
          apply le_antisymm
          · repeat rw [← @sInf_eq_iInf', ← @intersection_Neighbourhood]
            rw [@le_ciInf_iff']
            simp only [Prod.forall, Subtype.forall]
            intro a ha b hb
            refine ciInf_le_of_le ?_ ⟨⟨a, (by
              simp only [Sublocale.nhds, Set.mem_ofPred_eq]
              use a)⟩, ⟨b, (by
              simp only [Sublocale.nhds, Set.mem_ofPred_eq]
              use b)⟩⟩ ?_
            · use 0
              simp [lowerBounds]
            simp only
            rw [← Measure.caratheodory.open_eq_toFun]
            apply Measure.caratheodory.mono
            rw [Open.preserves_inf]
          · simp only [OrderBot.bddBelow, le_ciInf_iff, Prod.forall, Subtype.forall]
            intro a ha b hb
            simp only [Sublocale.nhds, Set.mem_ofPred_eq] at ha hb
            rcases ha with ⟨a', ⟨ha1, ha2⟩⟩
            rcases hb with ⟨b', ⟨hb1, hb2⟩⟩
            refine ciInf_le_of_le ?_ ⟨⟨a', (by
              rw [← @sInf_eq_iInf', ← Sublocale.intersection_Neighbourhood]
              exact ha1)⟩, ⟨b', (by
              rw [← @sInf_eq_iInf', ← Sublocale.intersection_Neighbourhood]
              exact hb1)⟩⟩ ?_
            · use 0
              simp [lowerBounds]
            · simp only
              rw [← Measure.caratheodory.open_eq_toFun]
              apply Measure.caratheodory.mono
              simp only [Open.preserves_inf, le_inf_iff]
              exact ⟨(by exact inf_le_of_left_le ha2),(by exact inf_le_of_right_le hb2)⟩
        · simp only [decreasingly_filtered, le_inf_iff, Prod.exists, Subtype.exists,
            exists_and_left, exists_prop, Prod.forall, Subtype.forall]
          intro a1 h1 a2 h2 a3 h3 a4 h4
          use a1 ⊓ a3
          refine ⟨nhds_inf_closed A a1 h1 a3 h3, ?_⟩
          use a2 ⊓ a4
          refine ⟨⟨?_, ?_⟩, ?_, nhds_inf_closed B a2 h2 a4 h4, ?_⟩
          · exact (inf_le_left : (a1 ⊓ a3) ⊓ (a2 ⊓ a4) ≤ a1 ⊓ a3).trans inf_le_left
          · exact (inf_le_right : (a1 ⊓ a3) ⊓ (a2 ⊓ a4) ≤ a2 ⊓ a4).trans inf_le_left
          · exact (inf_le_left : (a1 ⊓ a3) ⊓ (a2 ⊓ a4) ≤ a1 ⊓ a3).trans inf_le_right
          · exact (inf_le_right : (a1 ⊓ a3) ⊓ (a2 ⊓ a4) ≤ a2 ⊓ a4).trans inf_le_right
    · exact ENNReal.coe_injective
  apply_fun (· + m.caratheodory (A ⊓ B))
  · ring_nf
    have h3 : m.caratheodory (A ⊔ B) + m.caratheodory (A ⊓ B) =
        ⨅ v_a : openNhds A, ⨅ w_b : openNhds B,
          m.toFun (v_a ⊔ w_b) +  m.toFun (v_a ⊓ w_b) := by
      conv =>
        enter [1]
        rw [h1, h2]
      apply_fun ENNReal.ofNNReal
      · simp only [ENNReal.coe_add]
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
        · simp_all only [nonempty_subtype, ENNReal.coe_add, le_iInf_iff, iInf_le_iff,
          Subtype.forall, Subtype.coe_prop, implies_true]
        · simp_all only [nonempty_subtype, ENNReal.coe_add, le_iInf_iff, iInf_le_iff,
          Subtype.forall]
          intro a b a_1 b_1 a_2 b_2 a_3 b_3 b_4 a_4
          obtain ⟨w, h⟩ := h_n_1
          obtain ⟨w_1, h_1⟩ := h_n_2
          let h1 := a_4 a b a_1 b_1
          let h2 := a_4 a_2 b_2 a_3 b_3
          let h3 := a_4 (a ⊓ a_2) (by exact openNhds_inf_closed a b a_2 b_2)
            (a_1 ⊓ a_3) (by exact openNhds_inf_closed a_1 b_1 a_3 b_3)
          apply le_trans h3
          apply add_le_add
          · norm_cast
            apply Measure.mono
            apply sup_le_sup inf_le_left inf_le_left
          · norm_cast
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
    have h6 : ⨅ v_a : openNhds A, ⨅ w_b : openNhds B,
        m.toFun ↑v_a + m.toFun ↑w_b  =
        (⨅ v_a : openNhds A, m.toFun ↑v_a) +
          ⨅ w_b : openNhds B, m.toFun ↑w_b := by
      rw [@NNReal.eq_iff]
      simp only [NNReal.coe_iInf, NNReal.coe_add]
      rw [ciInf_add]
      conv =>
        enter [2, 1, i]
        rw [add_ciInf (by use 0; simp[lowerBounds])]
      use 0
      simp [lowerBounds]
    rw [h6]
    have h7 : m.caratheodory (A ⊓ B) +
        (m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B)) =
        m.caratheodory A + m.caratheodory B := by
      rw [@add_tsub_cancel_iff_le]
      have h : m.caratheodory A ≤ m.caratheodory A + m.caratheodory B := by
        exact le_self_add
      apply le_trans' h
      apply Measure.caratheodory.mono
      exact inf_le_left
    rw [h7]
    rw [add_eq_add_iff_eq_and_eq] <;> simp [Measure.caratheodory, sInf_image']
  · exact add_left_injective (caratheodory (A ⊓ B))


/-- Example: strict additivity of the Caratheodory measure on sublocales, a direct
consequence of `Measure.caratheodory.strictly_additive`. -/
theorem Beispiel (A B : Sublocale E) :
    m.caratheodory (A ⊔ B) = m.caratheodory A + m.caratheodory B - m.caratheodory (A ⊓ B) := by
  exact Measure.caratheodory.strictly_additive A B

#print axioms Beispiel



#print axioms Measure.caratheodory.strictly_additive
