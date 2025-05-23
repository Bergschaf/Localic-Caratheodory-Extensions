import Leroy.Measure.Regular


variable {E' : Type*} [Order.Frame E']


def Sublocale.embed {A : Sublocale E'} (b : Sublocale (Image A)) : Sublocale E' where
  toFun x := (f_untenstern (Nucleus.frameHom A)) (b ((Nucleus.frameHom A) x)) -- TODO ohne f_untenstern
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

lemma Image_himp_closed (A : Sublocale E') (a b : E') (h1 : a ∈ Image A) (h2 : b ∈ Image A) : a ⇨ b ∈ Image A := by
  simp [Image] at *
  apply le_antisymm
  . simp
    conv =>
      enter [1, 2]
      rw [← h1]
    conv =>
      enter [2]
      rw [← h2]
    rw [← A.map_inf]
    apply A.monotone
    rw [← le_himp_iff]
  . exact Nucleus.le_apply



@[simp] -- Wichtig, TODO woanders
lemma Nucleus.frameHom.of_coe (A : Sublocale E') (i : Image A) : A.frameHom i = i := by
  simp [Nucleus.frameHom]
  rw [@Subtype.ext_iff_val]
  simp only [Set.val_codRestrict_apply]
  let test := i.prop
  simp only [Image, Set.mem_setOf_eq] at test
  exact test


def Sublocale.restrict (A : Sublocale E') (b : Sublocale E') (h : b ≤ A): Sublocale (Image A) where
  toFun x := A.frameHom (b x)
  map_inf' x y := by
    simp
    rw [GaloisConnection.u_inf A.gc', b.map_inf,map_inf]
  idempotent' x := by
    simp
    simp [Nucleus.frameHom]
    rw [← Subtype.coe_le_coe]
    simp only [Set.val_codRestrict_apply]
    conv =>
      enter [2, 2]
      rw [← b.idempotent]
      rw [← b.idempotent]

    apply A.monotone
    apply b.monotone
    simp [Sublocale.le_iff] at h
    apply h

  le_apply' x := by
    simp [Nucleus.frameHom]
    rw [← Subtype.coe_le_coe]
    simp only [Set.val_codRestrict_apply]
    apply le_trans b.le_apply
    apply le_trans A.le_apply
    rfl

-- TODO woanders
lemma Sublocale.embed_le (A : Sublocale E') (b : Sublocale (Image A)) : A.embed b ≤ A := by
  have h : A.embed b ≤ A.embed ⊤ := by
    apply Sublocale.embed.mono
    apply le_top
  apply le_trans h
  rw [Sublocale.embed_top]

lemma Sublocale.restrict_mono (A : Sublocale E') (b a : Sublocale E') (h1: b ≤ A) (h2 : a ≤ A) : a ≤ b → A.restrict a h2 ≤ A.restrict b h1 := by
  intro h3
  simp [Sublocale.restrict]
  intro i
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  gcongr
  apply h3

lemma Sublocale.restrict_embed (A : Sublocale E') (b : Sublocale (Image A)) : A.restrict (A.embed b) (Sublocale.embed_le _ _)= b := by
  ext i
  simp [Sublocale.restrict, Sublocale.embed, f_untenstern_eq_val]
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp only [Nucleus.frameHom.of_coe]

lemma Sublocale.embed_restrict (A : Sublocale E') (b : Sublocale E') (h : b ≤ A) : A.embed (A.restrict b h) = b := by
  simp [embed, f_untenstern_eq_val, restrict]
  ext i
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk]
  simp [Nucleus.frameHom]
  simp [Sublocale.le_iff] at h
  apply le_antisymm
  . conv =>
      enter [2]
      rw [← b.idempotent]
    apply le_trans' (h (b i))
    apply A.monotone
    conv =>
      enter [2]
      rw[ ← b.idempotent]
    apply b.monotone
    exact h _
  . apply le_trans' A.le_apply
    apply b.monotone
    exact A.le_apply


def Sublocale.restrict_open (A : Sublocale E') (u : Open E') : Open (Image A) where
  element := A.frameHom u


lemma Sublocale.embed_restrict_open (A : Sublocale E') (u : Open E') : A.embed (A.restrict_open u) = A ⊓ u := by
  rw [Sublocale.embed_open_eq_inf]
  apply le_antisymm
  . simp only [le_inf_iff, inf_le_left, true_and]
    intro i
    rw [Sublocale.inf_apply]
    simp [Open.toSublocale, Sublocale.le_iff, Sublocale.restrict_open]
    rw [Nucleus.coe_mk, InfHom.coe_mk]
    intro a ha h1
    have h2 := h1 ↑((Nucleus.frameHom A) i)
    simp at h2
    have h_help : OrderDual.toDual a = a := by rfl
    simp [h_help] at *
    --rw [← a.idempotent]
    --apply le_trans' (ha (a i))
    simp [Nucleus.frameHom] at h2 h1
    let h3 := h1 (a i)
    rw [a.idempotent] at h3
    --
    apply le_trans A.le_apply
    apply le_trans' h3
    simp
    rw [← A.map_inf]
    apply le_trans' (ha _)
    apply A.monotone
    simp only [himp_inf_self, inf_le_left]

  . simp only [le_inf_iff, inf_le_left, true_and]
    intro i
    rw [Sublocale.inf_apply]
    simp [Open.toSublocale, Sublocale.le_iff, Sublocale.restrict_open]
    rw [Nucleus.coe_mk, InfHom.coe_mk]
    intro a ha h1
    apply le_trans' (h1 i)
    apply himp_le_himp
    simp [Nucleus.frameHom]
    . exact A.le_apply
    . rfl

lemma Sublocale.embed_orderiso (A : Sublocale E') (a b : Sublocale (Image A)) : A.embed a ≤ A.embed b → a ≤ b := by
  intro h
  simp [embed, f_untenstern_eq_val, Sublocale.le_iff] at h
  repeat rw [Nucleus.coe_mk, InfHom.coe_mk] at h
  intro i
  let h1 := h i
  simp at h1
  exact h1

lemma Sublocale.restrict_orderiso (A : Sublocale E') (a b : Sublocale E') (h1 : a ≤ A) (h2 : b ≤ A): A.restrict a h1 ≤ A.restrict b h2 → a ≤ b := by
  intro h
  apply_fun A.embed at h
  repeat rw [Sublocale.embed_restrict] at h
  exact h
  exact embed.mono A

lemma Sublocale.restrict_open_eq_restrict (A : Sublocale E') (u : Open E') : (A.restrict_open u).toSublocale = A.restrict (A ⊓ u) (by simp) := by
  --- TODO eleganter damit, dass embed injective ist
  apply le_antisymm
  . apply  Sublocale.embed_orderiso
    rw [Sublocale.embed_restrict_open]
    rw [Sublocale.embed_restrict]

  . apply  Sublocale.embed_orderiso
    rw [Sublocale.embed_restrict_open]
    rw [Sublocale.embed_restrict]

/-lemma commutes leider nicht [e_regular : Fact (regular E')] (A : Sublocale E') (s : Set (Open E')) : A ⊓ (sSup s).toSublocale = ⨆ b : (Open.toSublocale '' s), A ⊓ b := by
  apply le_antisymm




    rw [← Sublocale.restrict_open_eq_inf]


    rw [← Sublocale.embed_open_sSup]
    apply Sublocale.embed.mono
    rw [← Open.le_iff]
    simp only [sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro a h2
    rw [Sublocale.restrict_open]
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    rw [well_inside_iff] at h2 ⊢
    rcases h2 with ⟨c, ⟨h2, h3⟩⟩
    use A.restrict_open c
    simp [Sublocale.restrict_open]
    apply And.intro
    . simp [Open.inf_def, Open.ext_iff]
      rw [eq_bot_iff] at h2 ⊢
      sorry
    . rw [eq_top_iff] at h3 ⊢
      apply_fun A.frameHom.toFun at h3
      simp  [Open.top_element, InfHom.toFun_eq_coe, InfTopHom.coe_toInfHom, map_top,
        FrameHom.coe_toInfTopHom, top_le_iff] at h3
      rw [Open.le_def]
      simp
      rw [← h3]
      simp [Open.sup_def]
      simp only [Monotone, Nucleus.frameHom, InfHom.toFun_eq_coe, InfHom.coe_mk]
      intro a b h
      rw [← Subtype.coe_le_coe]
      simp only [Set.val_codRestrict_apply]
      apply A.monotone h

  .
    conv =>
      enter [1, 1]
      rw [Sublocale.intersection_Open_Neighbourhhood A]
    rw [sInf_image]
    rw [biInf_inf]
    conv =>
      enter [1, 1, i, 1, h]
      rw [← Open.preserves_inf]
    have h1 (i : Open E') : i ⊓ sSup s = ⨆ a : s, i ⊓ a := by
      ext
      simp [Open.inf_def, Open.sSup_def]
      rw [inf_sSup_eq]
      simp
      conv =>
        enter [2, 1]
        rw [iSup]
      simp [Open.sSup_def, sSup_image]
      apply le_antisymm
      . simp_all only [le_iSup_iff, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂, implies_true]
      . simp_all only [le_iSup_iff, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂, implies_true]
    conv =>
      enter [1, 1, i, 1, h, 1]
      rw [h1]
    rw [Sublocale.intersection_Open_Neighbourhhood (iSup _)]
    simp only [le_sInf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a h2
    simp only [iInf_le_iff, le_iInf_iff, OrderDual.forall]
    intro b h3


    have h4 : a ∈ A.Open_Neighbourhood := by
      simp [Sublocale.Open_Neighbourhood] at h2 ⊢










  . simp only [Open.preserves_sSup, le_inf_iff, iSup_le_iff, inf_le_left, implies_true,
    Subtype.forall, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    intro a ha
    apply le_trans inf_le_right
    apply le_sSup
    simp
    use a-/




/-- TODO woanders-/
lemma Sublocale.Image_regular' [e_regular : Fact (regular E')] (A : Sublocale E') : regular (Image A):= by
  simp [regular]
  intro u
  apply le_antisymm
  . rw [Open.le_iff]
    refine Sublocale.embed_orderiso A u _ ?_
    have h_regular : regular E' := by
      apply e_regular.elim
    rw [Sublocale.embed_open_eq_inf]

    rw [h_regular ⟨_⟩]
    refine Sublocale.restrict_orderiso A _ _ (by simp) (by exact embed_le A (sSup {V | V ≪ u}).toSublocale) ?_
    rw [← Sublocale.restrict_open_eq_restrict]
    rw [Sublocale.restrict_embed]
    simp [← Open.le_iff, Sublocale.restrict_open, Open.le_def, Open.sSup_def]
    intro a h
    --
    apply le_sSup
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use ⟨A.frameHom a.element⟩
    simp [well_inside_iff] at h ⊢
    rcases h with ⟨c, ⟨h1, h2⟩⟩
    use A.restrict_open c
    apply And.intro
    . simp [Sublocale.restrict_open, Open.inf_def, Open.ext_iff]
      rw [eq_bot_iff] at h1
      apply_fun A.frameHom.toFun at h1
      simp at h1
      rw [← h1]
      rw [Open.inf_def, map_inf]
      simp
      exact OrderHomClass.mono (Nucleus.frameHom A)
    . simp [Sublocale.restrict_open, Open.sup_def, Open.ext_iff] at h2
      rw [eq_top_iff] at h2 ⊢
      apply_fun A.frameHom.toFun at h2
      simp at h2
      rw [eq_top_iff] at h2
      apply le_trans h2
      simp [Open.sup_def, Sublocale.restrict_open]
      simp
      exact OrderHomClass.mono (Nucleus.frameHom A)

  . simp
    intro b h
    exact le_of_well_inside _ _ h

variable (A : Sublocale E') (m : @Measure E' _) [Fact (regular E')]

noncomputable def Measure.restrict_sublocale : Open (Image A) → NNReal :=
  fun x ↦ m.caratheodory (A.embed x) -- ist das richtig?

noncomputable def Measure.restrict_sublocale_measure : @Measure (Image A) _ where
  toFun := Measure.restrict_sublocale A m

  empty := by
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
    rw [@inf_sup_left]


  filtered s h := by
    by_cases hC : Nonempty s
    . simp_rw [Measure.restrict_sublocale]
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
                . use m.caratheodory ⊤
                  simp only [upperBounds, Set.mem_image, exists_exists_and_eq_and, Set.mem_range,
                    forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
                  intro a
                  by_cases hC :  Nonempty (∃ a_1 ∈ s, { element := ↑a_1.element } = a)
                  . apply ciSup_le
                    intro _
                    exact caratheodory.le_top m (A ⊓ a.toSublocale)
                  . rw [not_nonempty_iff] at hC
                    rw [@ciSup_of_empty]
                    . exact bot_le

                . refine le_ciSup_of_le ?_ ?_ ?_
                  . use m.caratheodory ⊤
                    simp only [upperBounds, Set.mem_range, Set.mem_image, exists_exists_and_eq_and,
                      Open.mk.injEq, exists_eq_right, exists_prop, and_imp, forall_exists_index,
                      Set.mem_setOf_eq]
                    intro _ _ _ _ h
                    rw [← h]
                    apply caratheodory.le_top

                  . simp
                    use u
                  rfl
              . use m.caratheodory ⊤
                simp [upperBounds]
                intro h
                apply Measure.caratheodory.mono
                apply OrderTop.le_top
            . use m.caratheodory ⊤
              simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
                Set.mem_setOf_eq]
              intro a
              apply ciSup_le'
              intro h
              apply caratheodory.le_top

          . rw [ciSup_le_iff']
            . intro i
              rw [ciSup_le_iff']
              . simp
                intro x hx h1
                rw [← h1]
                refine le_ciSup_of_le ?_ x ?_
                . use m.caratheodory ⊤
                  simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
                    Set.mem_setOf_eq]
                  intro a
                  apply ciSup_le'
                  intro _
                  apply caratheodory.le_top

                refine le_ciSup_of_le ?_ hx ?_
                . use m.caratheodory ⊤
                  simp [upperBounds]
                  intro _
                  apply caratheodory.le_top
                rfl
              . use m.caratheodory ⊤
                simp only [upperBounds, Set.mem_range, Set.mem_image, exists_exists_and_eq_and,
                  exists_prop, and_imp, forall_exists_index, Function.const_apply, Set.mem_setOf_eq]
                intro _ _ _ _ h
                rw [← h]
                apply caratheodory.le_top
            . use m.caratheodory ⊤
              simp only [upperBounds, Set.mem_image, exists_exists_and_eq_and, Set.mem_range,
                forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
              intro a
              apply ciSup_le'
              intro _
              apply caratheodory.le_top

        rw [h_help]
        ---
        rw [← Measure.inf_filtered]
        ----
        rw [Sublocale.embed_open_sSup]
        ---
        conv =>
          enter [1, 1, 1, a, 1]
          rw [Sublocale.embed_open_eq_inf]
        rw [Measure.inf_commutes_sSup]
        apply congrArg
        apply le_antisymm <;> simp [le_iSup_iff]
        rw [increasingly_filtered] at *
        simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]

        intro a ha b hb
        obtain ⟨w, ⟨h1, h2, h3⟩⟩ := h a ha b hb
        use w
        simp only [h1, true_and]
        apply And.intro
        . exact h2
        . exact h3

        rw [increasingly_filtered] at *
        simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]

        intro a ha b hb
        obtain ⟨w, ⟨h1, h2, h3⟩⟩ := h a ha b hb
        use w
        simp only [h1, true_and]
        apply And.intro
        . exact h2
        . exact h3


      . exact Set.Nonempty.of_subtype
      . use m.caratheodory ⊤
        simp [upperBounds]
        intro _ _
        apply caratheodory.le_top
      . simp only [csSup_empty, bot_eq_zero', zero_le]
    . have h : s = ∅ := by
        exact Set.not_nonempty_iff_eq_empty'.mp hC
      simp [h]
      rw [Measure.restrict_sublocale, Open.bot_toSublocale, Sublocale.embed_bot]
      rw [Measure.caratheodory.bot_eq_0]
