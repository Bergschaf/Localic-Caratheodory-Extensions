import Leroy.Basic
import Leroy.Nucleus

variable {X E : Type*} [Order.Frame X] [Order.Frame E]
open CategoryTheory


def Image (e : Nucleus X) : Set X :=
  {v : X | e v = v}

--def Nucleus.embedding {n : Nucleus E} : Nucleus E → X :=

instance : Coe (Nucleus X) (Set X) where
  coe  := fun x ↦ Image x
-- TODO ggf le sSup und so als instance definieren

variable {n : Nucleus E}


def e_schlange : E → Image n := Set.codRestrict n (Image n) (by intro x; simp [Image]; exact Nucleus.idempotent)


instance sup : Max (Image n) where
  max x y := e_schlange (x ⊔ y)

instance inf : Min (Image n) where
  min x y := e_schlange (x ⊓ y)




instance supSet : SupSet (Image n) := ⟨fun x ↦ e_schlange (sSup x)⟩
instance infSet : InfSet (Image n) := ⟨fun x ↦ e_schlange (sInf x)⟩
instance top : Top (Image n) := ⟨e_schlange ⊤⟩
instance bot : Bot (Image n) := ⟨e_schlange ⊥⟩




instance image_frame (n : Nucleus E) : Order.Frame (Image n) := by

  let embedding : Image n → E := fun x ↦ x


  have inf_ (a b : Image n) : e_schlange (a.val ⊓ b)  = a ⊓ b  := by
    simp [inf]




  have h_e (a : Image n) :  a = e_schlange a.val := by
    sorry


  have e_schlange_monotone : Monotone e_schlange := by
      simp only [Monotone, Set.codRestrict, Subtype.mk_le_mk, e_schlange]
      exact fun ⦃a b⦄ a_1 => OrderHomClass.GCongr.mono n a_1

  have aux1 : ∀ (a b : ↑Image n), a ≤ a ⊔ b := by
    intro a b
    simp [sup]
    have h_2 (c d : E) : c ≤ c ⊔ d := by exact SemilatticeSup.le_sup_left c d
    let h3 := h_2 a b

    let h8 := le_of_eq (h_e a)
    apply_fun (e_schlange) at h3
    apply le_trans h8 h3
    exact e_schlange_monotone

  have sup_comm : ∀ (a b : ↑Image n), a ⊔ b = b ⊔ a := by
    intro a b
    simp only [sup]
    rw [sup_comm]


  have aux2 : ∀ (a b : ↑Image n), b ≤ a ⊔ b := by
    intro a b
    rw [sup_comm]
    apply aux1


  have aux3 : ∀ (a b c : ↑Image n), a ≤ c → b ≤ c → a ⊔ b ≤ c := by
    intro a b c h1 h2
    simp [sup]
    let h3 := sup_le h1 h2
    rw [h_e c]
    apply_fun e_schlange at h3
    exact h3
    exact e_schlange_monotone

  have aux4 : ∀ (a b : ↑Image n), a ⊓ b ≤ a := by
    intro a b
    simp [inf]
    have h_2 (c d : E) : c ⊓ d ≤ c := by exact inf_le_left
    let h3 := h_2 a b

    let h8 := le_of_eq (h_e a)
    apply_fun (e_schlange) at h3
    apply le_trans h3
    rw [← h_e]
    exact e_schlange_monotone

  have inf_comm : ∀ (a b : ↑Image n), a ⊓ b = b ⊓ a := by
    intro a b
    simp only [inf]
    rw [inf_comm]


  have aux5 : ∀ (a b : ↑Image n), a ⊓ b ≤ b := by
    intro a b
    rw [inf_comm]
    apply aux4

  have aux6 : ∀ (a b c : ↑Image n), a ≤ b → a ≤ c → a ≤ b ⊓ c := by
    intro a b c h1 h2
    simp [inf]
    let h3 := le_inf h1 h2
    rw [h_e c]
    apply_fun e_schlange at h3
    rw [← h_e]
    rw [← h_e] at h3
    exact h3
    exact e_schlange_monotone

  have aux7 : ∀ (s : Set ↑Image n), ∀ a ∈ s, a ≤ sSup s := by
    intro s a h
    simp [supSet]
    rw [h_e a]
    let s1 : Set E := s
    let a1 : E := a
    have h1 : a1 ∈ s1 := by
      simp [s1,a1,h]
    let h2 := le_sSup h1
    apply_fun e_schlange at h2
    exact h2
    apply e_schlange_monotone

  have aux8 : ∀ (s : Set ↑Image n) (a : ↑Image n), (∀ b ∈ s, b ≤ a) → sSup s ≤ a := by
    intro s a h
    simp only [supSet]
    let s1 : Set E := s
    let a1 : E := a
    have h1 : ∀ b ∈ s1, b ≤ a1 := by
      simp [s1, a1]
      intro b x h2
      let h3 := h ⟨b, x⟩
      let h4 := h3 h2
      apply h4

    let h2 := sSup_le h1
    apply_fun e_schlange at h2
    rw [h_e a]
    simp [h2]
    exact h2
    exact e_schlange_monotone

  have aux9 : ∀ (s : Set ↑Image n), ∀ a ∈ s, sInf s ≤ a := by
    intro s a h
    simp [infSet]
    rw [h_e a]
    let s1 : Set E := s
    let a1 : E := a
    have h1 : a1 ∈ s1 := by
      simp [s1,a1,h]
    let h2 := sInf_le h1
    apply_fun e_schlange at h2
    exact h2
    apply e_schlange_monotone


  have aux10 : ∀ (s : Set ↑Image n) (a : ↑Image n), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
    intro s a h
    simp only [infSet]
    let s1 : Set E := s
    let a1 : E := a
    have h1 : ∀ b ∈ s1, a1 ≤ b:= by
      simp [s1, a1]
      intro b x h2
      let h3 := h ⟨b, x⟩
      let h4 := h3 h2
      apply h4

    let h2 := le_sInf h1
    apply_fun e_schlange at h2
    rw [h_e a]
    simp [h2]
    exact h2
    exact e_schlange_monotone


  have aux11 : ∀ (x : ↑Image n), x ≤ ⊤ := by
    simp only [Subtype.forall]
    intro a h
    simp [top]
    have h1 : a ≤ ⊤ := by
      exact OrderTop.le_top a
    apply_fun e_schlange at h1
    rw [h_e ⟨a, h⟩]
    apply h1
    exact e_schlange_monotone

  have aux12 : ∀ (x : ↑Image n), ⊥ ≤ x := by
    simp only [Subtype.forall]
    intro a h
    simp [bot]
    have h1 : ⊥ ≤ a := by
        exact OrderBot.bot_le a
    apply_fun e_schlange at h1
    rw [h_e ⟨a, h⟩]
    apply h1
    exact e_schlange_monotone


  have h1 (a b : ↑Image n) : (a : E) ⊓ (b : E) = a ⊓ b:= by
    have h2 : (a : E) ⊓ (b : E) ∈ Image n := by
      simp only [Image, Set.mem_setOf_eq, Image n]
      rw [h_e a,h_e b]
      simp [e_schlange, Nucleus.idempotent]
    simp [Image n, Image] at h2
    simp [inf, e_schlange, h2]
  have h_test (s : Set ↑Image n) : ↑(sSup s) ∈ Image n := by
    exact Subtype.coe_prop (sSup s)



  let semilatticesup : SemilatticeSup Image n := ⟨sup.max, aux1, aux2, aux3⟩
  let lattice : Lattice Image n := ⟨inf.min, aux4, aux5, aux6⟩
  let completelattice : CompleteLattice Image n := ⟨aux7, aux8, aux9, aux10, aux11, aux12⟩


  have e_schlange_preserves_inf : ∀ (a b : E), e_schlange (a ⊓ b) = e_schlange a ⊓ e_schlange b := by
    intro a b
    let h2 := @n.map_inf _ _ a b
    have h3 : e_schlange (a ⊓ b) = n (a ⊓ b) := by
      simp [e_schlange]
    let h4 := Eq.trans h3 h2
    let h5 := h1 (e_schlange a) (e_schlange b)
    let h6 := Eq.trans h4 h5
    exact SetCoe.ext h6

  have e_schlange_idempotent : ∀ (a : E), e_schlange (e_schlange a) = e_schlange a := by
    exact fun a => Eq.symm (SetCoe.ext (congrArg Subtype.val (h_e (e_schlange a))))

  have leroy_aux1 : ∀ (a : ↑Image n) (s : Set ↑Image n), a ⊓ sSup s = e_schlange (a ⊓ sSup s) := by
    intro a s
    simp [supSet]
    rewrite [h_e a]
    rw [e_schlange_preserves_inf]
    rw [e_schlange_idempotent]

  have h_e_image (s : Set E) :∀ x, x ∈ Image n -> e_schlange x = x := by
    intro x h
    simp [e_schlange]
    exact h

  have h_e_image1 (x : E) : x ∈ Image n -> e_schlange ↑x = x := by
    exact fun a => h_e_image Image n x (h_e_image Image n x a)

  have h_e_image2 (x : ↑Image n) : e_schlange x = x := by
    exact Eq.symm (SetCoe.ext (congrArg Subtype.val (h_e x)))

  have h_e_image3 (x : E) : (h : x ∈ Image n) -> e_schlange x = ⟨x, h⟩ := by
    exact fun h => SetCoe.ext (h_e_image Image n x (h_e_image Image n x h))


  have aux13 : ∀ (a : ↑Image n) (s : Set ↑Image n), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
    intro a s
    rw [leroy_aux1]
    rw [inf_sSup_eq]
    simp [iSup, inf, sSup]

    have a_inf_b_mem : ∀ (b : ↑Image n), ↑a ⊓ ↑b ∈ Image n := by
      intro b
      simp [Image n, Image]
      rw [h_e ↑a]
      rw [h_e ↑b]
      simp [e_schlange, n.idempotent]

    have h14 : sSup ((Set.range fun b => sSup (Set.range fun (h : b ∈ Subtype.val '' s) => ↑a ⊓ b))) ≤ sSup ((Subtype.val '' Set.range fun b => e_schlange (sSup (Subtype.val '' Set.range fun (h : b∈ s) => e_schlange (↑a ⊓ ↑b))))) := by
        simp only [Set.range]
        simp only [Set.mem_image]
        simp
        intro a1 ha1 ha2
        apply le_sSup
        simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
          exists_eq_right]
        have h_eq : a1 = ↑(⟨a1, ha1⟩ : Image n) := by
          rfl
        have h : ↑a ⊓ a1 ∈ Image n := by
          rw [h_eq]
          apply a_inf_b_mem

        use h
        use a1
        use ha1
        have h1 : {x | ⟨a1, ha1⟩ ∈ s ∧ e_schlange (↑a ⊓ a1) = x} = {a ⊓ ⟨a1, ha1⟩} := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          apply Iff.intro
          . rintro ⟨h2, h3⟩
            rw [← h3]
            rw [h_e_image3 (↑a ⊓ a1) h]
            exact h_e ⟨↑a ⊓ a1, h⟩
          . intro h2
            apply And.intro
            . exact ha2
            . rw [h2]
              rw [h_e_image3 (↑a ⊓ a1) h]
              exact h_e ⟨↑a ⊓ a1, h⟩
        rw [h1]
        simp
        rw [h_e_image3]
        simp only [Subtype.coe_prop, Subtype.coe_eta]
        exact h_e_image3 (↑a ⊓ ↑(⟨a1, ha1⟩ : Image n)) ((Iff.of_eq (Eq.refl (↑a ⊓ a1 ∈ Image n))).mpr h)
        exact
          h_e_image Image n (↑(a ⊓ ⟨a1, ha1⟩))
            (h_e_image1 (↑(a ⊓ ⟨a1, ha1⟩)) (congrArg n (a_inf_b_mem ⟨a1, ha1⟩)))

    apply_fun e_schlange at h14
    exact h14
    exact e_schlange_monotone

  let frame : Order.Frame ↑(Image n) := Order.Frame.ofMinimalAxioms ⟨aux13⟩
  exact frame

instance inst_frame (n : Nucleus E): Order.Frame (Image n) := image_frame n



lemma nucleus_frameHom_exists (n : Nucleus E) : (∃ f : FrameHom E (Image n), n = ((f_obenstern f) ⋙ (f_untenstern f)).obj ∧ ∃ _ : Leroy_Embedding f, true) :=  by
  let Image n := Image n

  let e_schlange : E → Image n := Set.codRestrict n Image n (by intro x; simp [Image n, Image]; apply n.idempotent)

  let embedding : Image n → E := fun x ↦ x

  let sup : Max Image n := ⟨fun x y ↦ e_schlange (x ⊔ y)⟩
  let inf : Min Image n := ⟨fun x y ↦ e_schlange (x ⊓ y)⟩

  have inf_ (a b : Image n) :e_schlange (a ⊓ b)  = a ⊓ b  := by
    simp [inf]

  let supSet : SupSet Image n := ⟨fun x ↦ e_schlange (sSup x)⟩
  let infSet : InfSet Image n := ⟨fun x ↦ e_schlange (sInf x)⟩
  let top : Top Image n := ⟨e_schlange ⊤⟩
  let bot : Bot Image n := ⟨e_schlange ⊥⟩

  have h_e (a : Image n) :  a = e_schlange a := by
    apply Eq.symm
    simp [Image n, Image, e_schlange]
    obtain ⟨val, property⟩ := a
    simp_all only [Image n]
    ext : 1
    simp_all only [Set.mem_setOf_eq, Set.val_codRestrict_apply]
    simp_all only [Image n]
    exact property

  have e_schlange_monotone : Monotone e_schlange := by
      simp only [Monotone, Set.codRestrict, Subtype.mk_le_mk, e_schlange]
      exact fun ⦃a b⦄ a_1 => OrderHomClass.GCongr.mono n a_1
  have h1 (a b : ↑Image n) : (a : E) ⊓ (b : E) = a ⊓ b:= by
    have h2 : (a : E) ⊓ (b : E) ∈ Image n := by
      simp only [Image, Set.mem_setOf_eq, Image n]
      rw [h_e a,h_e b]
      simp [e_schlange, n.idempotent]
    simp [Image n, Image] at h2
    simp [inf, e_schlange, h2]

  have h_test (s : Set ↑Image n) : ↑(sSup s) ∈ Image n := by
    exact Subtype.coe_prop (sSup s)


  have e_schlange_preserves_inf : ∀ (a b : E), e_schlange (a ⊓ b) = e_schlange a ⊓ e_schlange b := by
    intro a b
    let h2 := @n.map_inf _ _ a b
    have h3 : e_schlange (a ⊓ b) = n (a ⊓ b) := by
      simp [e_schlange]
    let h4 := Eq.trans h3 h2
    let h5 := h1 (e_schlange a) (e_schlange b)
    let h6 := Eq.trans h4 h5
    exact SetCoe.ext h6


  have e_schlange_idempotent : ∀ (a : E), e_schlange (e_schlange a) = e_schlange a := by
    exact fun a => Eq.symm (SetCoe.ext (congrArg Subtype.val (h_e (e_schlange a))))


  have aux43 : ∀ (s : Set E), e_schlange (sSup s) = sSup ((fun a => e_schlange a) '' s) := by
    intro s
    apply le_antisymm_iff.mpr
    apply And.intro
    . simp [supSet]
      have h0 : ∀ x ∈ s, x ≤ e_schlange x := by
        intro x h
        simp [e_schlange]
        apply (n.le_apply)
      have h1 : sSup s ≤ sSup (Subtype.val '' ((fun a => e_schlange a) '' s)) := by
        apply sSup_le
        intro b h
        have h2 : e_schlange b ≤ sSup (Subtype.val '' ((fun a => e_schlange a) '' s))  := by
          apply le_sSup
          simp
          use b
        apply le_trans (h0 b h) h2
      apply_fun e_schlange at h1
      exact h1
      apply e_schlange_monotone

    . have h0 :∀ x ∈ s,x ≤  sSup s := by
        exact fun x a => CompleteLattice.le_sSup s x a
      have h1 : ∀ x ∈ s, e_schlange x ≤ e_schlange (sSup s) := by
        intro x h
        let h0 := h0 x h
        apply_fun e_schlange at h0
        exact h0
        exact e_schlange_monotone
      apply sSup_le
      intro b h
      simp at h
      rcases h with ⟨x, ⟨h2, h3⟩⟩
      let h1 := h1 x h2
      rw [← h3]
      exact h1

  let Image ntype := ↑Image n


  let frameHom : FrameHom E Image ntype := ⟨⟨⟨e_schlange, e_schlange_preserves_inf⟩, (by simp[e_schlange,inst_frame];exact rfl)⟩, aux43⟩
  use frameHom
  apply And.intro
  . ext x
    simp [f_obenstern, f_untenstern, Functor.comp_obj, frameHom, e_schlange]
    apply le_antisymm_iff.mpr
    apply And.intro
    . apply le_sSup
      simp
      have h : ∀ a b : ↑Image n, (a : E) ≤ (b : E) → a ≤ b := by
        simp only [Subtype.coe_le_coe, imp_self, implies_true]
      apply h
      simp only [Subtype.coe_le_coe, inf, e_schlange, Image n, supSet, frameHom]
      repeat rw [FrameHom.coe_mk]
      simp only [InfTopHom.coe_mk, InfHom.coe_mk, inf, e_schlange, Image n, supSet, frameHom]
      exact le_of_eq (e_schlange_idempotent x)

    . apply sSup_le
      simp
      intro b h
      apply_fun (fun (x : ↑Image n) ↦ (x : E)) at h
      simp at h
      have h1: b ≤ n b := by
        exact n.le_apply
      exact Preorder.le_trans b (n b) (n x) h1 h
      exact fun ⦃a b⦄ a => a
  . have h : Function.Surjective (f_obenstern frameHom).obj := by
      simp [Function.Surjective, frameHom]
      intro a h
      simp[Image ntype,Image n,Image] at h
      use a
      simp [f_obenstern, e_schlange]
      exact SetCoe.ext h
    let embedding : Leroy_Embedding frameHom := ⟨f_surjective_one frameHom h⟩
    use embedding


noncomputable def nucleus_frameHom (n : Nucleus E) : {f : FrameHom E (Image n) // n.toFun = (f_untenstern f).obj ∘ (f_obenstern f).obj ∧ Fact (Leroy_Embedding f)} := by
  let f := Classical.choose (nucleus_frameHom_exists n)
  let p := Classical.choose_spec (nucleus_frameHom_exists n)
  let p1 := p.right
  let p2 := Classical.choose p1
  let pl := p.left
  let pr := p.right
  refine ⟨?val, ?property⟩
  exact f
  apply And.intro
  . exact pl
  . exact { out := p2 }


lemma nucleus_equiv_subframe_1 : (∃ (X : Type u),∃ _ : Order.Frame X, ∃ f : FrameHom E X, e = ((f_obenstern f) ⋙ (f_untenstern f)).obj ∧ ∃ _ : Leroy_Embedding f, true) → (∃ (X : Type u),∃ _ : Order.Frame X, ∃ f : FrameHom E X, e =((f_obenstern f) ⋙ (f_untenstern f)).obj) := by
  intro a
  simp_all only
  obtain ⟨w, h⟩ := a
  obtain ⟨w_1, h⟩ := h
  obtain ⟨w_2, h⟩ := h
  obtain ⟨left, right⟩ := h
  obtain ⟨w_3, h⟩ := right
  subst left
  simp_all only
  apply Exists.intro
  · apply Exists.intro
    · apply Exists.intro
      · rfl


lemma frameHom_nucleus : (∃ (X : Type u),∃ _ : Order.Frame X, ∃ f : FrameHom E X, e =((f_obenstern f) ⋙ (f_untenstern f)).obj) →  (∃ n : Nucleus E,e = n) := by
  intro h
  rcases h with ⟨X, h, f, h1⟩
  have n_1 :  ∀ (x : E), e (e x) ≤ e x := by
    intro x
    subst h1
    simp_all only [f_obenstern, f_untenstern, Functor.comp_obj, map_sSup, sSup_le_iff,
      Set.mem_setOf_eq]
    intro a h
    apply le_sSup
    simp only [Set.mem_setOf_eq]
    apply le_trans h
    simp only [sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, imp_self, implies_true]


  have n_2 : (x : E) → x ≤ e x := by
    intro x
    subst h1
    simp [f_untenstern, f_obenstern]
    apply le_sSup
    simp only [Set.mem_setOf_eq, le_refl]

  have n_3 :  ∀ (x y : E), e (x ⊓ y) = e x ⊓ e y := by
    intro x y
    subst h1
    simp [f_untenstern, f_obenstern]
    apply le_antisymm_iff.mpr
    apply And.intro
    . apply sSup_le
      intro b h
      simp
      simp at h
      rcases h with ⟨h1, h2⟩
      apply And.intro
      . apply le_sSup
        simp [h1]
      . apply le_sSup
        simp[h2]
    . apply le_sSup
      simp only [Set.mem_setOf_eq, map_inf, map_sSup]
      rw [sSup_inf_sSup]
      simp only [Set.mem_prod, Set.mem_image, Set.mem_setOf_eq, iSup_le_iff, and_imp,
        forall_exists_index, Prod.forall]
      apply And.intro
      . intro a b x1 h1 h2 x2 h3 h4
        subst h2
        subst h4
        exact inf_le_of_left_le h1
      . intro a b x1 h1 h2 x2 h3 h4
        subst h2 h4
        exact inf_le_of_right_le h3
  use ⟨⟨e, n_3⟩, n_1, n_2⟩
  rfl
