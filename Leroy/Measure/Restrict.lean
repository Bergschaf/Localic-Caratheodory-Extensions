module

public import Leroy.Measure.Regular
public import Leroy.Nucleus_Image

/-!
# Restrictions of sublocales and measures

This file develops the restriction theory for sublocales and measures on a frame `E'`.
A sublocale `A` of `E'` induces a frame homomorphism onto the image of its nucleus, and
every sublocale of the image can be embedded back into `E'` below `A`. Restriction and
embedding form a Galois insertion on sublocales and an isomorphism on opens, which is
then used to restrict a measure on `E'` to the sublocale `A` via restriction of its
Caratheodory measure.
-/

@[expose] public section

variable {E' : Type*} [Order.Frame E']

/-- Interpret a sublocale `A` of `E'` as a frame homomorphism from `E'` to the image
of its nucleus `A.toNucleus`. This package `A.toNucleus.frameHom` so that sublocales
thus obtained can be compared with, and restricted from, the ambient frame. -/
def Sublocale.frameHom (A : Sublocale E') : FrameHom E' (Image A.toNucleus) :=
  A.toNucleus.frameHom

/-- The nucleus underlying a sublocale is a Galois connection between the frame
homomorphism `A.frameHom` and the coercion `Subtype.val` of the image. -/
theorem Sublocale.gc' (A : Sublocale E') :
    GaloisConnection A.frameHom Subtype.val :=
  Nucleus.gc' A.toNucleus

/-- The nucleus underlying a sublocale is a Galois connection between the frame
homomorphism `A.frameHom` and its meet-preserving upper adjoint `lowerStar`.
This is the form of the adjunction used to compute the embedding of sublocales. -/
theorem Sublocale.gc (A : Sublocale E') :
    GaloisConnection A.frameHom (lowerStar A.frameHom) :=
  Nucleus.gc A.toNucleus

/-- As a simp lemma: the frame homomorphism of a sublocale fixes every point of the
image of the nucleus, since such points already lie in the image. -/
@[simp] lemma Nucleus.frameHom.of_coe (A : Sublocale E') (i : Image A.toNucleus) :
    A.frameHom i = i := by
  apply Subtype.ext
  simpa only [Sublocale.frameHom, Nucleus.frameHom_apply_val] using
    (mem_Image A.toNucleus).mp i.property

/-- Embed a sublocale `b` of the image of the nucleus `A.toNucleus` back into `E'`:
the result is the meet of `A` with the pullback of `b`, a sublocale of `E'` lying below
`A`. Together with `Sublocale.restrictSublocale` this realizes the set of sublocales
below `A` as the lattice of sublocales of the image. -/
def Sublocale.embed {A : Sublocale E'} (b : Sublocale (Image A.toNucleus)) : Sublocale E' :=
  ({
    toFun x := (lowerStar A.frameHom) (b (A.frameHom x))
    idempotent' x := by
      simp only [lowerStar, map_sSup, sSup_le_iff, Set.mem_ofPred_eq]
      intro c h
      simp only [le_sSup_iff, upperBounds, Set.mem_ofPred_eq]
      intro d h1'
      apply h1'
      apply le_trans h
      conv =>
        enter [2]
        rw [← b.idempotent]
      apply b.monotone
      simp only [sSup_le_iff, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, imp_self, implies_true]

    map_inf' c d := by
      simp only [InfHomClass.map_inf, apply_eq_toNucleus, toNucleus_apply]
      rw [GaloisConnection.u_inf A.gc]

    le_apply' a := by
      simp only [apply_eq_toNucleus, toNucleus_apply]
      apply le_sSup
      simp only [Set.mem_ofPred_eq]
      change A.frameHom a ≤ b.toNucleus (A.frameHom a)
      exact b.toNucleus.le_apply
  } : Nucleus E').toSublocale

/-- Computing the embedded sublocale `A.embed b` pointwise: it sends `x` to the lower
adjoint applied to `b` at the value of `A` on `x`. -/
@[simp] lemma Sublocale.embed_apply (A : Sublocale E')
  (b : Sublocale (Image A.toNucleus)) (x : E') :
  A.embed b x = lowerStar A.frameHom (b (A.frameHom x)) := by
  simp [Sublocale.embed]

/-- The embedding of the largest sublocale of the image is `A` itself, showing that the
embedding is surjective at the top and hence compatible with restriction. -/
lemma Sublocale.embed_top (A : Sublocale E') : A.embed ⊤ = A := by
  ext x
  rw [Sublocale.embed_apply]
  rw [Sublocale.top_apply]
  change lowerStar A.toNucleus.frameHom (A.toNucleus.frameHom x) = A.toNucleus x
  rw [lowerStar_eq_val A.toNucleus]
  exact Nucleus.frameHom_apply_val A.toNucleus x

/-- The embedding of the smallest sublocale of the image is the smallest sublocale,
so the embedding preserves both bounds of the lattice of sublocales. -/
lemma Sublocale.embed_bot (A : Sublocale E') : A.embed ⊥ = ⊥ := by
  ext x
  rw [Sublocale.embed_apply]
  simp only [Sublocale.bot_apply]
  change lowerStar A.toNucleus.frameHom (⊤ : Image A.toNucleus) = ⊤
  rw [lowerStar_eq_val A.toNucleus]
  rfl

/-- On opens the embedding has an explicit form: embedding the open `u` of the image
yields the restriction of `u` to `A`, i.e. the meet `A ⊓ ⟨u.element⟩` inside `E'`.
This identifies the embedded opens with the restriction of opens to the sublocale. -/
lemma Sublocale.embed_open_eq_inf (A : Sublocale E') (u : Open (Image A.toNucleus)) :
    A.embed u = A ⊓ (⟨u.element⟩ : Open E') := by
  apply le_antisymm
  · apply le_inf
    · apply (Sublocale.le_iff _ _).mpr
      intro x
      rw [Sublocale.embed_apply]
      apply (A.gc _ _).mp
      have hA : A.frameHom (A x) = A.frameHom x := by
        simpa [Sublocale.frameHom] using
          Nucleus.frameHom.of_coe A (A.frameHom x)
      rw [hA]
      rw [Open.toSublocale_apply]
      exact le_himp_iff.mpr inf_le_left
    · apply (Sublocale.le_iff _ _).mpr
      intro x
      rw [Sublocale.embed_apply]
      apply (A.gc _ _).mp
      simp only [Open.toSublocale_apply]
      apply le_himp_iff.mpr
      calc
        A.frameHom ((u.element : E') ⇨ x) ⊓ u.element =
            A.frameHom ((u.element : E') ⇨ x) ⊓ A.frameHom (u.element : E') := by
              rw [Nucleus.frameHom.of_coe]
        _ = A.frameHom (((u.element : E') ⇨ x) ⊓ (u.element : E')) :=
          (InfHomClass.map_inf A.frameHom _ _).symm
        _ ≤ A.frameHom x := OrderHomClass.mono A.frameHom (by
          rw [himp_inf_self]
          exact inf_le_left)
  · let V : Sublocale E' := (⟨(u.element : E')⟩ : Open E').toSublocale
    apply (Sublocale.le_iff _ _).mpr
    intro x
    rw [Sublocale.inf_apply]
    simp only [lowerBounds_insert, lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic,
      le_inf_iff, le_iInf_iff, and_imp]
    intro b hbA hbV
    rw [Sublocale.embed_apply, lowerStar, sSup_le_iff]
    intro y hy
    have hA : A x ≤ b x := (Sublocale.le_iff b A).mp hbA x
    have hU : (u.element : E') ⇨ A x ≤ b (A x) := by
      have h := (Sublocale.le_iff b V).mp hbV (A x)
      simpa [V, Open.toSublocale, Open.toNucleus] using h
    have hU' : u.toSublocale (A.frameHom x) ≤ A.frameHom (b (A x)) := by
      rw [Open.toSublocale_apply]
      rw [← Nucleus.frameHom_map_himp A.toNucleus u.element (A.frameHom x)]
      exact OrderHomClass.mono A.frameHom (by
        simpa only [Sublocale.frameHom, Nucleus.frameHom_apply_val,
          Sublocale.apply_eq_toNucleus] using hU)
    have hy' : A y ≤ b (A x) := by
      change A.frameHom y ≤ u.toSublocale (A.frameHom x) at hy
      have h := le_trans hy hU'
      have hval : (A.frameHom y : E') ≤ (A.frameHom (b (A x)) : E') :=
        Subtype.coe_le_coe.mp h
      have hAy : A y ≤ A (b (A x)) := by
        simp only [Sublocale.frameHom, Nucleus.frameHom_apply_val,
          Sublocale.apply_eq_toNucleus] at hval
        simpa only [Sublocale.apply_eq_toNucleus] using hval
      calc
        A y ≤ A (b (A x)) := hAy
        _ ≤ b (b (A x)) := (Sublocale.le_iff b A).mp hbA (b (A x))
        _ = b (A x) := b.idempotent _
    calc
      y ≤ A y := A.le_apply y
      _ ≤ b (A x) := hy'
      _ ≤ b (b x) := b.monotone hA
      _ = b x := b.idempotent x

/-- The embedding of sublocales distributes over binary joins of opens of the image,
because it is computed via a meet with `A`, which is right adjoint on opens. -/
lemma Sublocale.embed_open_sup (A : Sublocale E') (u v : Open (Image A.toNucleus)) :
    A.embed (u ⊔ v) = A.embed u ⊔ A.embed v := by
  ext i
  simp_rw [Sublocale.embed_apply, Sublocale.frameHom,
    lowerStar_eq_val A.toNucleus]
  rw [Sublocale.sup_apply]
  rw [GaloisConnection.u_inf A.gc']
  simp only [Sublocale.sup_apply, Sublocale.embed_apply, Sublocale.frameHom,
    lowerStar_eq_val A.toNucleus]


-- sSup analaog

/-- The embedding of sublocales is order preserving: `b ≤ c` in the image implies
`A.embed b ≤ A.embed c` in `E'`. -/
lemma Sublocale.embed.mono (A : Sublocale E') : Monotone A.embed := by
  intro b c h
  apply (Sublocale.le_iff _ _).mpr
  intro i
  simp only [embed, Nucleus.toSublocale_apply]
  exact GaloisConnection.monotone_u A.gc
    ((Sublocale.le_iff _ _).mp h (A.frameHom i))

/-- Restrict a sublocale `b` of `E'` that lies below `A` to a sublocale of the image of
`A.toNucleus`, by composing `b` with the frame homomorphism of `A`. This is left
adjoint to the embedding `Sublocale.embed`. -/
def Sublocale.restrictSublocale (A : Sublocale E') (b : Sublocale E') (h : b ≤ A) :
    Sublocale (Image A.toNucleus) :=
  ({
  toFun x := A.frameHom (b x)
  map_inf' x y := by
    change A.frameHom (b ((x : E') ⊓ (y : E'))) =
      A.frameHom (b x) ⊓ A.frameHom (b y)
    rw [b.map_inf]
    exact InfHomClass.map_inf A.frameHom _ _
  idempotent' x := by
    change A.frameHom (b (A.frameHom (b (x : E')))) ≤
      A.frameHom (b (x : E'))
    apply OrderHomClass.mono A.frameHom
    have hinner : b (A (b (x : E'))) ≤ b (x : E') := by
      calc
        b (A (b (x : E'))) ≤ b (b (b (x : E'))) :=
          b.monotone ((Sublocale.le_iff b A).mp h (b (x : E')))
        _ = b (x : E') := by simp
    simpa only [Sublocale.frameHom, Nucleus.frameHom_apply_val,
      Sublocale.apply_eq_toNucleus] using hinner
  le_apply' x := by
    calc
      x = A.frameHom x := (Nucleus.frameHom.of_coe A x).symm
      _ ≤ A.frameHom (b (x : E')) :=
        OrderHomClass.mono A.frameHom (b.le_apply _)
  } : Nucleus (Image A.toNucleus)).toSublocale

/-- Computing the restricted sublocale pointwise: `A.restrictSublocale b h` sends a
point of the image of `A.toNucleus` to `A` applied to `b` of the point. -/
@[simp] lemma Sublocale.restrictSublocale_apply (A : Sublocale E')
    (b : Sublocale E') (h : b ≤ A) (x : Image A.toNucleus) :
    A.restrictSublocale b h x = A.frameHom (b x) := by
  unfold Sublocale.restrictSublocale
  rw [Nucleus.toSublocale_apply]
  rfl

-- TODO woanders
/-- Every embedded sublocale lies below `A`, so the image of `Sublocale.embed`
consists precisely of sublocales of `E'` below `A`. -/
lemma Sublocale.embed_le (A : Sublocale E') (b : Sublocale (Image A.toNucleus)) :
    A.embed b ≤ A := by
  have h : A.embed b ≤ A.embed ⊤ := by
    apply Sublocale.embed.mono
    apply le_top
  apply le_trans h
  rw [Sublocale.embed_top]

/-- Restriction is order reversing: for sublocales `a`, `b` below `A`, `a ≤ b` implies
`A.restrictSublocale a ≤ A.restrictSublocale b`, since restriction post-composes with
the monotone frame homomorphism of `A`. -/
lemma Sublocale.restrict_mono (A : Sublocale E') (b a : Sublocale E') (h1 : b ≤ A)
    (h2 : a ≤ A) : a ≤ b → A.restrictSublocale a h2 ≤ A.restrictSublocale b h1 := by
  intro h3
  apply (Sublocale.le_iff _ _).mpr
  intro i
  rw [Sublocale.restrictSublocale_apply, Sublocale.restrictSublocale_apply]
  exact OrderHomClass.mono A.frameHom ((Sublocale.le_iff a b).mp h3 (i : E'))

/-- Restricting an embedded sublocale gives back the original sublocale: the frame
homomorphism of `A` acts as the identity on points of the image, so restriction is
surjective into sublocales of the image. -/
lemma Sublocale.restrict_embed (A : Sublocale E') (b : Sublocale (Image A.toNucleus)) :
    A.restrictSublocale (A.embed b) (Sublocale.embed_le _ _) = b := by
  ext i
  rw [Sublocale.restrictSublocale_apply, Sublocale.embed_apply,
    Sublocale.frameHom, lowerStar_eq_val A.toNucleus]
  exact congrArg Subtype.val <|
    (Nucleus.frameHom.of_coe A (b (A.frameHom i))).trans
      (congrArg b (Nucleus.frameHom.of_coe A i))

/-- Embedding a restricted sublocale gives back the original sublocale: for `b ≤ A`
the Galois insertion of restriction and embedding recovers `b`, so embedding is
injective and restriction surjective onto the sublocales below `A`. -/
lemma Sublocale.embed_restrict (A : Sublocale E') (b : Sublocale E') (h : b ≤ A) :
    A.embed (A.restrictSublocale b h) = b := by
  ext i
  rw [Sublocale.embed_apply, Sublocale.frameHom, lowerStar_eq_val A.toNucleus,
    Sublocale.restrictSublocale_apply]
  simp only [Sublocale.frameHom, Nucleus.frameHom_apply_val]
  have h' := (Sublocale.le_iff b A).mp h
  have hbAi : b (A.toNucleus i) = b i := by
    apply le_antisymm
    · calc
        b (A.toNucleus i) ≤ b (b i) := b.monotone (h' i)
        _ = b i := b.idempotent i
    · exact b.monotone A.toNucleus.le_apply
  rw [hbAi]
  apply le_antisymm
  · calc
      A.toNucleus (b i) ≤ b (b i) := by
        simpa only [Sublocale.apply_eq_toNucleus] using h' (b i)
      _ = b i := b.idempotent _
  · exact A.toNucleus.le_apply

/-- Restrict an open `u` of `E'` to an open of the image of `A.toNucleus` by mapping its
element through the frame homomorphism of `A`. -/
def Sublocale.restrict_open (A : Sublocale E') (u : Open E') : Open (Image A.toNucleus) where
  element := A.frameHom u


/-- For opens, embedding after restriction computes the meet with `A`, i.e. the
sublocale corresponding to `A ⊓ u`. This makes the frame of opens of the image
isomorphic to the opens below `A` in `E'`. -/
lemma Sublocale.embed_restrict_open (A : Sublocale E') (u : Open E') :
    A.embed (A.restrict_open u) = A ⊓ u := by
  rw [Sublocale.embed_open_eq_inf]
  apply SetLike.ext
  intro i
  rw [Sublocale.mem_inf, Sublocale.mem_inf]
  let v : Open E' := ⟨A.frameHom u.element⟩
  have hA_imp (hi : A.toNucleus i = i) :
      A.toNucleus (u.element ⇨ i) = A.toNucleus u.element ⇨ i := by
    apply le_antisymm
    · apply le_himp_iff.mpr
      calc
        A.toNucleus (u.element ⇨ i) ⊓ A.toNucleus u.element =
            A.toNucleus ((u.element ⇨ i) ⊓ u.element) := by
          exact (A.toNucleus.map_inf' _ _).symm
        _ ≤ A.toNucleus i := A.toNucleus.monotone
          (le_himp_iff.mp (le_rfl : u.element ⇨ i ≤ u.element ⇨ i))
        _ = i := hi
    · calc
        A.toNucleus u.element ⇨ i ≤ u.element ⇨ i := by
          apply le_himp_iff.mpr
          calc
            (A.toNucleus u.element ⇨ i) ⊓ u.element ≤
                (A.toNucleus u.element ⇨ i) ⊓ A.toNucleus u.element :=
              inf_le_inf_left _ A.toNucleus.le_apply
            _ ≤ i := le_himp_iff.mp
              (le_rfl : A.toNucleus u.element ⇨ i ≤ A.toNucleus u.element ⇨ i)
        _ ≤ A.toNucleus (u.element ⇨ i) :=
          A.toNucleus.le_apply (x := u.element ⇨ i)
  constructor
  · rintro ⟨hiA, hiV⟩
    have hAfix : A i = i := (Sublocale.mem_iff_apply_eq A i).mp hiA
    change A.toNucleus i = i at hAfix
    have hVfix : v.element ⇨ i = i := by
      simpa only [Open.toSublocale_apply] using
        (Sublocale.mem_iff_apply_eq v.toSublocale i).mp hiV
    have hAui : A.toNucleus (u.element ⇨ i) = i := by
      calc
        A.toNucleus (u.element ⇨ i) = A.toNucleus u.element ⇨ i :=
          hA_imp hAfix
        _ = v.element ⇨ i := by
          simp only [v, Sublocale.frameHom, Nucleus.frameHom_apply_val]
        _ = i := hVfix
    have hui : u.element ⇨ i = i := le_antisymm
      (by
        simpa only [hAui] using
          (A.toNucleus.le_apply (x := u.element ⇨ i)))
      (le_himp_iff.mpr inf_le_left)
    exact ⟨hiA, (Sublocale.mem_iff_apply_eq u.toSublocale i).mpr (by
      simpa only [Open.toSublocale_apply] using hui)⟩
  · rintro ⟨hiA, hiU⟩
    have hAfix : A i = i := (Sublocale.mem_iff_apply_eq A i).mp hiA
    change A.toNucleus i = i at hAfix
    have hUfix : u.element ⇨ i = i := by
      simpa only [Open.toSublocale_apply] using
        (Sublocale.mem_iff_apply_eq u.toSublocale i).mp hiU
    have hVfix : v.element ⇨ i = i := by
      calc
        v.element ⇨ i = A.toNucleus u.element ⇨ i := by
          simp only [v, Sublocale.frameHom, Nucleus.frameHom_apply_val]
        _ = A.toNucleus (u.element ⇨ i) := (hA_imp hAfix).symm
        _ = A.toNucleus i := by rw [hUfix]
        _ = i := hAfix
    exact ⟨hiA, (Sublocale.mem_iff_apply_eq v.toSublocale i).mpr (by
      simpa only [Open.toSublocale_apply] using hVfix)⟩

/-- The embedding is injective on sublocales: `A.embed a ≤ A.embed b` implies `a ≤ b`.
Hence the embedding is an order embedding onto the sublocales below `A`. -/
lemma Sublocale.embed_orderiso (A : Sublocale E') (a b : Sublocale (Image A.toNucleus)) :
    A.embed a ≤ A.embed b → a ≤ b := by
  intro h
  have h' := Sublocale.restrict_mono A (A.embed b) (A.embed a)
    (Sublocale.embed_le A b) (Sublocale.embed_le A a) h
  simpa only [Sublocale.restrict_embed] using h'

/-- The embedding maps suprema of sublocales of the image to suprema of the embedded
sublocales. This, combined with `Sublocale.embed_bot`, makes the embedding a frame
isomorphism onto the lattice of sublocales below `A`. -/
lemma Sublocale.embed_sSup (A : Sublocale E')
    (s : Set (Sublocale (Image A.toNucleus))) :
    A.embed (sSup s) = sSup (A.embed '' s) := by
  apply le_antisymm
  · let c := sSup (A.embed '' s)
    have hc : c ≤ A := by
      apply sSup_le
      rintro _ ⟨b, hb, rfl⟩
      exact Sublocale.embed_le A b
    have hsub : sSup s ≤ A.restrictSublocale c hc := by
      apply sSup_le
      intro b hb
      apply Sublocale.embed_orderiso A
      calc
        A.embed b ≤ c := le_sSup (Set.mem_image_of_mem A.embed hb)
        _ = A.embed (A.restrictSublocale c hc) := by
          rw [Sublocale.embed_restrict]
    calc
      A.embed (sSup s) ≤ A.embed (A.restrictSublocale c hc) :=
        Sublocale.embed.mono A hsub
      _ = c := by rw [Sublocale.embed_restrict]
  · apply sSup_le
    rintro _ ⟨b, hb, rfl⟩
    exact Sublocale.embed.mono A (le_sSup hb)

/-- The embedding preserved by suprema, reformulated on opens: embedding the sublocale
generated by the supremum of a set of opens of the image yields the supremum of the
embedded opens, identified via `Sublocale.embed_open_eq_inf`. -/
lemma Sublocale.embed_open_sSup (A : Sublocale E')
    (s : Set (Open (Image A.toNucleus))) :
    A.embed (sSup s).toSublocale = ⨆ a ∈ s, embed a.toSublocale := by
  rw [Open.preserves_sSup, Sublocale.embed_sSup]
  simp only [Set.image_image, sSup_image]

/-- Restriction is order reflecting: for sublocales `a`, `b` below `A`, the restricted
sublocales being ordered forces `a ≤ b`, because the embedding is injective
(`Sublocale.embed_orderiso` together with `Sublocale.embed_restrict`). -/
lemma Sublocale.restrict_orderiso (A : Sublocale E') (a b : Sublocale E') (h1 : a ≤ A)
    (h2 : b ≤ A) : A.restrictSublocale a h1 ≤ A.restrictSublocale b h2 → a ≤ b := by
  intro h
  apply_fun A.embed at h
  repeat rw [Sublocale.embed_restrict] at h
  · exact h
  exact embed.mono A

/-- Restricting an open and then generating a sublocale agrees with directly restricting
the sublocale `A ⊓ u`: both routes embed back to `A ⊓ u`, and the embedding is
injective. -/
lemma Sublocale.restrict_open_eq_restrict (A : Sublocale E') (u : Open E') :
    (A.restrict_open u).toSublocale = A.restrictSublocale (A ⊓ u) (by simp) := by
  --- TODO eleganter damit, dass embed injective ist
  apply le_antisymm
  · apply  Sublocale.embed_orderiso
    rw [Sublocale.embed_restrict_open]
    rw [Sublocale.embed_restrict]
  · apply  Sublocale.embed_orderiso
    rw [Sublocale.embed_restrict_open]
    rw [Sublocale.embed_restrict]

/-- TODO woanders
If `E'` is a regular frame then so is the image of the nucleus of any sublocale `A`:
regularity, formulated via the way-below relation on well-inside opens, restricts
along the embedding of opens of the image, which preserves the witness decompositions
given by regularity in `E'`. -/
lemma Sublocale.Image_regular' [e_regular : Fact (regular E')] (A : Sublocale E') :
    regular (Image A.toNucleus) := by
  simp only [regular]
  intro u
  apply le_antisymm
  · rw [Open.le_iff]
    refine Sublocale.embed_orderiso A u _ ?_
    have h_regular : regular E' := by
      apply e_regular.elim
    rw [Sublocale.embed_open_eq_inf]
    rw [h_regular ⟨_⟩]
    refine Sublocale.restrict_orderiso A _ _ (by simp)
      (by exact embed_le A (sSup {V | V ≪ u}).toSublocale) ?_
    rw [← Sublocale.restrict_open_eq_restrict]
    rw [Sublocale.restrict_embed]
    simp only [restrict_open, Open.sSup_def, map_sSup, ← Open.le_iff, Open.le_def,
      sSup_le_iff, Set.mem_image, Set.mem_ofPred_eq, exists_exists_and_eq_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    --
    apply le_sSup
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    use ⟨A.frameHom a.element⟩
    simp only [well_inside_iff] at h ⊢
    refine ⟨?_, trivial⟩
    rcases h with ⟨c, ⟨h1, h2⟩⟩
    use A.restrict_open c
    apply And.intro
    · simp only [restrict_open, Open.inf_def, Open.ext_iff, Open.bot_element]
      have h1elem : c.element ⊓ a.element = ⊥ := by
        simpa only [Open.inf_def, Open.bot_element] using congrArg Open.element h1
      have h1map : A.frameHom (c.element ⊓ a.element) = ⊥ := by
        calc
          A.frameHom (c.element ⊓ a.element) = A.frameHom ⊥ :=
            congrArg A.frameHom h1elem
          _ = ⊥ := by
            let : Order.Frame (↑(Image A.toNucleus)) := image_frame A.toNucleus
            change A.toNucleus.frameHom ⊥ = ⊥
            exact BotHomClass.map_bot A.toNucleus.frameHom
      exact (InfHomClass.map_inf A.frameHom _ _).symm.trans h1map
    · apply Open.ext
      have h2elem : c.element ⊔ (u.element : E') = ⊤ := by
        simpa only [Open.sup_def, Open.top_element] using congrArg Open.element h2
      have h2map : A.toNucleus.frameHom c.element ⊔
          A.toNucleus.frameHom (u.element : E') = ⊤ := by
        simpa only [Sublocale.frameHom, map_sup, map_top] using
          congrArg A.frameHom h2elem
      have hcoe : A.toNucleus.frameHom (u.element : E') = u.element := by
        simpa only [Sublocale.frameHom] using Nucleus.frameHom.of_coe A u.element
      rw [hcoe] at h2map
      simpa only [Open.sup_def, Open.top_element, Sublocale.restrict_open,
        Sublocale.frameHom] using h2map
  · simp only [sSup_le_iff, Set.mem_ofPred_eq]
    intro b h
    exact le_of_well_inside _ _ h

variable (A : Sublocale E') (m : @Measure E' _) [Fact (regular E')]

/-- The valuation underlying the restriction of the measure `m` to the sublocale `A`,
defined on an open of the image of `A.toNucleus` as the Caratheodory valuation of the
embedded open in `E'`. -/
noncomputable def Measure.restrict_sublocale : Open (Image A.toNucleus) → NNReal :=
  fun x ↦ m.caratheodory (A.embed x) -- ist das richtig?

/-- The restriction of the measure `m` on `E'` to the sublocale `A`, realized as a
measure on the frame of the image of `A.toNucleus`. It is the measure-theoretic
counterpart of the lattice-theoretic embedding of sublocales, and is the structure
produced when applying the Caratheodory extension theorem within `A`. -/
noncomputable def Measure.restrict_sublocale_measure : @Measure (Image A.toNucleus) _ where
  toFun := Measure.restrict_sublocale A m

  empty := by
    rw [Measure.restrict_sublocale, Open.bot_toSublocale, Sublocale.embed_bot]
    --todo lemma
    rw [Measure.caratheodory.bot_eq_0]


  mono := by
    simp only [Measure.restrict_sublocale]
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
    let U : Open E' := ⟨u.element⟩
    let V : Open E' := ⟨v.element⟩
    have h_open :
        ({ element := (Lattice.inf u.element v.element : Image A.toNucleus) } : Open E') =
          U ⊓ V := by
      apply Open.ext
      change ((u.element ⊓ v.element : ↑(Image A.toNucleus)) : E') =
        (u.element : E') ⊓ v.element
      exact Subtype.coe_inf
        (fun {x y} hx hy => by
          apply (mem_Image A.toNucleus).2
          calc
            A.toNucleus (x ⊓ y) = A.toNucleus x ⊓ A.toNucleus y :=
              A.toNucleus.map_inf' x y
            _ = x ⊓ y := by
              rw [(mem_Image A.toNucleus).mp hx, (mem_Image A.toNucleus).mp hy])
        u.element v.element
    have h_third :
        A ⊓ ({ element := (Lattice.inf u.element v.element : Image A.toNucleus) } :
          Open E').toSublocale =
          A ⊓ U.toSublocale ⊓ V.toSublocale := by
      rw [h_open, Open.preserves_inf, inf_assoc]
    rw [congrArg (fun b : Sublocale E' => m.caratheodory b) h_third]
    rw [← inf_sup_left, ← Open.preserves_sup, ← Measure.restrict_subadditive]
    exact congrArg (fun b : Sublocale E' => m.caratheodory (A ⊓ b))
      Open.preserves_sup


  filtered s h := by
    by_cases hC : Nonempty s
    · simp_rw [Measure.restrict_sublocale]
      rw [csSup_image]
      · simp_rw [Measure.restrict_sublocale]
        conv =>
          enter [2, 1, a, 1]
          rw [Sublocale.embed_open_eq_inf]
        have h_help : ⨆ a ∈ s, m.caratheodory (A ⊓ (⟨↑a.element⟩ : Open E').toSublocale) =
            ⨆ a ∈ (Open.mk '' (Subtype.val '' (Open.element '' s))),
              m.caratheodory (A ⊓ a.toSublocale) := by
          apply le_antisymm
          · rw [ciSup_le_iff']
            · intro u
              rw [ciSup_le_iff']
              · intro h
                · refine le_ciSup_of_le ?_ ⟨u.element.val⟩ ?_
                  · use m.caratheodory ⊤
                    simp only [upperBounds, Set.mem_image, exists_exists_and_eq_and, Set.mem_range,
                      forall_exists_index, forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
                    intro a
                    by_cases hC :  Nonempty (∃ a_1 ∈ s, { element := ↑a_1.element } = a)
                    · apply ciSup_le
                      intro _
                      exact caratheodory.le_top m (A ⊓ a.toSublocale)
                    · rw [not_nonempty_iff] at hC
                      rw [@ciSup_of_empty]
                      · exact bot_le
                  · refine le_ciSup_of_le ?_ ?_ ?_
                    · use m.caratheodory ⊤
                      simp only [upperBounds, Set.mem_range, Set.mem_image,
                        exists_exists_and_eq_and, Open.mk.injEq, exists_prop, and_imp,
                        forall_exists_index, Set.mem_ofPred_eq]
                      intro _ _ _ _ h
                      rw [← h]
                      apply caratheodory.le_top
                    · simp only [Set.mem_image, exists_exists_and_eq_and, Open.mk.injEq]
                      use u
                    rfl
              · use m.caratheodory ⊤
                simp only [upperBounds, Set.mem_range, forall_exists_index,
                  forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
                intro h
                apply Measure.caratheodory.mono
                apply OrderTop.le_top
            · use m.caratheodory ⊤
              simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
                Set.mem_ofPred_eq]
              intro a
              apply ciSup_le'
              intro h
              apply caratheodory.le_top
          · rw [ciSup_le_iff']
            · intro i
              rw [ciSup_le_iff']
              · simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp]
                intro x hx h1
                rw [← h1]
                refine le_ciSup_of_le ?_ x ?_
                · use m.caratheodory ⊤
                  simp only [upperBounds, Set.mem_range, forall_exists_index,
                    forall_apply_eq_imp_iff,
                    Set.mem_ofPred_eq]
                  intro a
                  apply ciSup_le'
                  intro _
                  apply caratheodory.le_top
                refine le_ciSup_of_le ?_ hx ?_
                · use m.caratheodory ⊤
                  simp only [upperBounds, Set.mem_range, forall_exists_index,
                    forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
                  intro _
                  apply caratheodory.le_top
                rfl
              · use m.caratheodory ⊤
                simp only [upperBounds, Set.mem_range, Set.mem_image, exists_exists_and_eq_and,
                  exists_prop, and_imp, forall_exists_index, Set.mem_ofPred_eq]
                intro _ _ _ _ h
                rw [← h]
                apply caratheodory.le_top
            · use m.caratheodory ⊤
              simp only [upperBounds, Set.mem_image, exists_exists_and_eq_and, Set.mem_range,
                forall_exists_index, forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
              intro a
              apply ciSup_le'
              intro _
              apply caratheodory.le_top
        rw [h_help]
        ---
        rw [← Measure.inf_filtered]
        swap
        · rw [increasingly_filtered] at *
          simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          intro a ha b hb
          obtain ⟨w, ⟨h1, h2, h3⟩⟩ := h a ha b hb
          use w
          simp only [h1, true_and]
          apply And.intro
          · exact h2
          · exact h3
        ----
        rw [Sublocale.embed_open_sSup]
        ---
        conv =>
          enter [1, 1, 1, a, 1]
          rw [Sublocale.embed_open_eq_inf]
        rw [Measure.inf_commutes_sSup]
        swap
        · rw [increasingly_filtered] at *
          simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂]
          intro a ha b hb
          obtain ⟨w, ⟨h1, h2, h3⟩⟩ := h a ha b hb
          use w
          simp only [h1, true_and]
          apply And.intro
          · exact h2
          · exact h3
        apply congrArg
        apply le_antisymm <;> simp [le_iSup_iff]
      · use m.caratheodory ⊤
        simp only [upperBounds, Set.mem_range, forall_exists_index,
          forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
        intro a
        apply Measure.caratheodory.mono
        apply OrderTop.le_top
      · simp only [csSup_empty, bot_eq_zero', zero_le]
    · have h : s = ∅ := by
        exact Set.not_nonempty_iff_eq_empty'.mp hC
      simp only [h, Measure.restrict_sublocale, Set.image_empty]
      have hs : (sSup (∅ : Set (Open ↑(Image A.toNucleus)))).toSublocale = ⊥ := by
        rw [sSup_empty, Open.bot_toSublocale]
      rw [hs, Sublocale.embed_bot, Measure.caratheodory.bot_eq_0]
      simp only [csSup_empty, bot_eq_zero']
