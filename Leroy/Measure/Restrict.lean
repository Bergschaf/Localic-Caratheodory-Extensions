import Leroy.Measure.Regular


variable {E' : Type*} [Order.Frame E']


def Sublocale.restrict_open (A : Sublocale E') (u : Open E') : Sublocale (Image A) where
  toFun i := (A.frameHom u.element) ⇨ i
  map_inf' x y := by
    sorry
  idempotent' := sorry
  le_apply' := sorry


def Sublocale.embed {A : Sublocale E'} (b : Sublocale (Image A)) : Sublocale E' where
  toFun x := (f_untenstern (Nucleus.frameHom A)) (b ((Nucleus.frameHom A) x))
  idempotent' x := by
    simp only [f_untenstern, map_sSup, sSup_le_iff, Set.mem_setOf_eq]
    intro c h
    --
    simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq]
    intro d h1'
    apply h1'
    apply le_trans h
    conv =>
      enter [2]
      rw [← b.idempotent]
    apply b.monotone
    simp only [sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, imp_self, implies_true]

  map_inf' c d := by
    simp
    rw [b.map_inf]
    rw [GaloisConnection.u_inf A.gc]

  le_apply' a := by
    simp [Nucleus.frameHom, f_untenstern]
    apply le_sSup
    simp
    exact b.le_apply

lemma Sublocale.embed_top (A : Sublocale E') : A.embed ⊤ = A := by
  simp [Sublocale.embed]
  ext x
  rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp [Nucleus.frameHom]
  simp [f_untenstern]
  apply le_antisymm
  . simp
    intro b h
    apply le_trans A.le_apply h
  . simp [le_sSup_iff, upperBounds]
    intro b h
    apply h
    refine Subtype.coe_le_coe.mp ?_
    simp
    rw [A.idempotent]


lemma Sublocale.embed_bot (A : Sublocale E') : A.embed ⊥ = ⊥ := by
  ext x
  simp [Sublocale.embed]
  rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp [f_untenstern]

lemma Sublocale.embed_open_eq_inf (A : Sublocale E') (u : Open (Image A)) : A.embed u = A ⊓ (⟨u.element⟩ : Open E') := by
  apply le_antisymm
  . apply le_inf
    . intro i
      simp only [embed, f_untenstern, Open.toSublocale, Nucleus.coe_mk, InfHom.coe_mk, le_sSup_iff,
        upperBounds, Set.mem_setOf_eq]
      rw [Nucleus.coe_mk, InfHom.coe_mk]
      intro b h
      apply h
      simp [← Subtype.coe_le_coe, Nucleus.frameHom]
      simp_rw [min, SemilatticeInf.inf, Lattice.inf]
      simp only [Set.val_codRestrict_apply, map_inf]
      rw [A.idempotent, A.idempotent, ← A.map_inf]
      apply A.monotone
      simp
    . simp only [Sublocale.embed, Open.toSublocale]
      intro i
      simp only [Nucleus.coe_mk, InfHom.coe_mk, f_untenstern, le_sSup_iff, upperBounds,
        Set.mem_setOf_eq]
      rw [Nucleus.coe_mk, InfHom.coe_mk]
      intro b h
      apply h
      simp [Nucleus.frameHom]
      rw [← Subtype.coe_le_coe]
      simp only [min, Set.val_codRestrict_apply]
      rw [SemilatticeInf.inf, Lattice.toSemilatticeInf]
      simp [Lattice.inf]
      --
      rw [A.idempotent, ← A.map_inf]
      apply A.monotone
      simp only [himp_inf_self, inf_le_left]
  . simp only [Open.toSublocale, Sublocale.embed]
    intro i
    rw [Sublocale.inf_apply]
    simp only [Nucleus.coe_mk, InfHom.coe_mk, lowerBounds_insert, lowerBounds_singleton,
      Set.Iic_inter_Iic, Set.mem_Iic, le_inf_iff, le_iInf_iff, and_imp, OrderDual.forall]
    repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
    intro a h1 h2
    simp only [f_untenstern, le_himp_iff, sSup_le_iff, Set.mem_setOf_eq]
    intro b h3
    rw [Sublocale.le_iff, Nucleus.coe_mk, InfHom.coe_mk] at h2
    rw [← Subtype.coe_le_coe] at h3
    simp_rw [min, SemilatticeInf.inf, Lattice.inf] at h3
    simp only [Nucleus.frameHom, FrameHom.coe_mk, InfTopHom.coe_mk, InfHom.coe_mk,
      Set.val_codRestrict_apply, map_inf] at h3
    rw [Sublocale.le_iff] at h1
    --
    let h2' := (h2 (a i))
    have h_help : (OrderDual.toDual a) = a := rfl
    rw [h_help] at h2'
    rw [a.idempotent] at h2'
    --apply_fun A.toFun at h2'
    let h3' := h3
    rw [A.idempotent, ← A.map_inf] at h3'
    apply le_trans' h2'
    simp only [le_himp_iff]
    apply le_trans' (h1 i)
    apply le_trans (A.le_apply) h3'

lemma Sublocale.embed_open_sup (A : Sublocale E') (u v : Open (Image A)) : A.embed (u ⊔ v) = A.embed u ⊔ A.embed v := by
  ext i
  simp_rw [Sublocale.embed, f_untenstern_eq_val, Sublocale.sup_apply]
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]

  rw [GaloisConnection.u_inf A.gc']



-- sSup analaog

lemma Sublocale.embed_open_sSup (A : Sublocale E') (s : Set (Open (Image A))) : A.embed (sSup s).toSublocale = ⨆ a ∈ s, embed a.toSublocale := by
  ext i
  simp_rw [Sublocale.embed, f_untenstern_eq_val, Sublocale.iSup_apply]
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  rw [Open.preserves_sSup, Sublocale.sSup_apply]
  --------
  rw [GaloisConnection.u_iInf₂ A.gc']
  ---------
  simp only [Set.mem_image, iInf_exists, exists_exists_and_eq_and, Open.toSublocale_apply, id_eq,
    InfHom.toFun_eq_coe]
  have h_help : ⨅ (i_1 : Sublocale (Image A)), ⨅ i_2 : Open (Image A), ⨅ (_ : i_2 ∈ s ∧ i_2.toSublocale = i_1), ↑((i_1 ((Nucleus.frameHom A) i)) : E') = ⨅ b ∈ s, ↑(b.toSublocale (A.frameHom i)) := by
    apply le_antisymm
    . simp only [Open.toSublocale_apply, le_iInf_iff, iInf_le_iff, and_imp,
      forall_apply_eq_imp_iff₂]
      intro i_1 i_2 b a
      simp_all only
    . simp only [Open.toSublocale_apply, le_iInf_iff, iInf_le_iff, and_imp,
      forall_apply_eq_imp_iff₂]
      intro a a_1 b a_2
      simp_all only

  rw [h_help]
  simp only [Open.toSublocale_apply]
  conv =>
    enter [2, 1, j]
    rw [iSup]
    simp only [sSup_apply, Set.mem_range, exists_prop, Open.toSublocale_apply, id_eq,
      InfHom.toFun_eq_coe]
  conv =>
    enter [2, 1, j, 1, j]
    rw [Nucleus.ext_iff,Nucleus.coe_mk, InfHom.coe_mk]

  apply le_antisymm
  . simp only [le_iInf_iff, iInf_le_iff, and_imp, OrderDual.forall]
    intro a b c d e f
    rw [← d]
    apply f
    apply c
  . simp only [le_iInf_iff, iInf_le_iff, and_imp, OrderDual.forall]
    intro a b c d

    let h := d a (A.embed (a.toSublocale)) b

    simp [Open.toSublocale, Sublocale.embed,f_untenstern_eq_val] at h
    have h_help : ∀ a : Nucleus E', OrderDual.toDual a = a := by
      exact fun a => rfl
    simp_rw [h_help, Nucleus.coe_mk, InfHom.coe_mk] at h
    conv at h =>
      enter [2]
      rw [Nucleus.coe_mk, InfHom.coe_mk]
      rw [Nucleus.coe_mk, InfHom.coe_mk]
    apply h
    intro j
    rw [Nucleus.coe_mk, InfHom.coe_mk]

/-lemma Sublocale.embed_open_sSup' (A : Sublocale E') (s : Set (Open (Image A))) : A.embed (sSup s).toSublocale = A ⊓ sSup (A.embed '' (Open.toSublocale '' s)) := by
  ext i
  simp_rw [Sublocale.embed, f_untenstern_eq_val]
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  rw [Open.preserves_sSup, Sublocale.sSup_apply]
  --------
  rw [GaloisConnection.u_iInf₂ A.gc']
  ---------
  simp [Sublocale.inf_apply]
  have h_help : ⨅ (i_1 : Sublocale (Image A)), ⨅ i_2 : Open (Image A), ⨅ (_ : i_2 ∈ s ∧ i_2.toSublocale = i_1), ↑((i_1 ((Nucleus.frameHom A) i)) : E') = ⨅ b ∈ s, ↑(b.toSublocale (A.frameHom i)) := by
    apply le_antisymm
    . simp only [Open.toSublocale_apply, le_iInf_iff, iInf_le_iff, and_imp,
      forall_apply_eq_imp_iff₂]
      intro i_1 i_2 b a
      simp_all only
    . simp only [Open.toSublocale_apply, le_iInf_iff, iInf_le_iff, and_imp,
      forall_apply_eq_imp_iff₂]
      intro a a_1 b a_2
      simp_all only

  rw [h_help]
  apply le_antisymm
  . simp [iInf_le_iff]
    intro b h1 h2 c h3
    sorry
  sorry-/





lemma Sublocale.embed.mono (A : Sublocale E') : Monotone A.embed := by
  intro b c h i
  simp only [embed, f_untenstern, Nucleus.coe_mk, InfHom.coe_mk, sSup_le_iff, Set.mem_setOf_eq]
  intro j h1
  simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq]
  intro k h2
  --
  apply h2
  rw [Sublocale.le_iff] at h
  apply le_trans' (h _)
  exact h1


variable (A : Sublocale E') (m : @Measure E' _) [Fact (regular E')]

noncomputable def Measure.restrict_sublocale : Open (Image A) → NNReal :=
  fun x ↦ m.caratheodory (A.embed x) -- ist das richtig?

noncomputable def Measure.restrict_sublocale_measure : @Measure (Image A) _ where
  toFun := Measure.restrict_sublocale A m

  filtered s h := by
    simp_rw [Measure.restrict_sublocale]
    rw [csSup_image]
    .
      conv =>
        enter [2, 1, a, 1]
        rw [Sublocale.embed_open_eq_inf]
      have h_help : ⨆ a ∈ s, m.caratheodory (A ⊓ (⟨↑a.element⟩ : Open E').toSublocale) = ⨆ a ∈ (Open.mk '' (Subtype.val '' (Open.element '' s))), m.caratheodory (A ⊓ a.toSublocale) := by
        apply le_antisymm
        . rw [ciSup_le_iff']
          . intro u
            rw [ciSup_le_iff']
            intro h
            . refine le_ciSup_of_le ?_ ⟨u.element.val⟩ ?_
              . sorry
              . refine le_ciSup_of_le ?_ ?_ ?_
                . sorry
                . simp
                  use u
                rfl
            . use m.caratheodory ⊤
              simp [upperBounds]
              intro h
              apply Measure.caratheodory.mono
              apply OrderTop.le_top
          . sorry --stimmt
        . rw [ciSup_le_iff']
          . intro i
            rw [ciSup_le_iff']
            . simp
              sorry -- stimmt
            . sorry -- stimmt
          . sorry

      rw [h_help]
      ---
      rw [← Measure.inf_filtered]
      ----
      rw [Sublocale.embed_open_sSup]
      ---
      conv =>
        enter [1, 1, 1, a, 1]
        rw [Sublocale.embed_open_eq_inf]

      sorry







    . sorry --by_cases oder so
    . use m.caratheodory ⊤
      simp [upperBounds]
      sorry
    . simp only [csSup_empty, bot_eq_zero', zero_le]
  /-empty := by
    rw [Measure.restrict_sublocale, Open.bot_toSublocale, Sublocale.embed_bot]
    --todo lemma
    rw [Measure.caratheodory.bot_eq_0]


  mono := by
    simp [Measure.restrict_sublocale]
    intro u v h
    apply Measure.caratheodory.mono
    apply Sublocale.embed.mono
    exact Open.le_iff.mp h

  strictly_additive u v := by
    rw [Measure.restrict_sublocale, Open.preserves_sup]
    rw [Sublocale.embed_open_sup]
    simp_rw [Measure.restrict_sublocale,Sublocale.embed_open_eq_inf]
    simp_rw [Open.inf_def]
    conv =>
      enter [2, 2, 1, 2, 1]
      simp [min,SemilatticeInf.inf]
    simp_rw [Lattice.inf]
    simp only [Set.val_codRestrict_apply, map_inf]
    rw [← Open.inf_def, Open.preserves_inf]
    let h_fix1 := Subtype.coe_prop u.element
    simp only [Image, Set.mem_setOf_eq] at h_fix1
    rw [h_fix1]
    let h_fix2 := Subtype.coe_prop v.element
    simp only [Image, Set.mem_setOf_eq] at h_fix2
    rw [h_fix2]
    rw [← inf_assoc]
    rw [← Measure.restrict_subadditive] -- wichtig
    apply congrArg
    rw [@inf_sup_left]-/
