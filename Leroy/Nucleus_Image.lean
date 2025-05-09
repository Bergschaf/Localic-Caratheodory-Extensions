--import Leroy.Basic
import Mathlib.Tactic
import Leroy.Nucleus

variable {X Y E : Type*} [Order.Frame X] [Order.Frame E] [Order.Frame Y]
open CategoryTheory


def Image (e : Nucleus X) : Set X :=
  {v : X | e v = v}

--def Nucleus.embedding {n : Nucleus E} : Nucleus E → X :=

instance : Coe (Nucleus X) (Set X) where
  coe  := fun x ↦ Image x
-- TODO ggf le sSup und so als instance definieren

variable {n : Nucleus E}


instance image_frame (n : Nucleus E) : Order.Frame (Image n) := by
  let img := Image n

  let e_schlange : E → img := Set.codRestrict n img (by intro x; simp [img, Image]; exact
    Nucleus.idempotent)

  let embedding : img → E := fun x ↦ x

  let sup : Max img := ⟨fun x y ↦ e_schlange (x ⊔ y)⟩
  let inf : Min img := ⟨fun x y ↦ e_schlange (x ⊓ y)⟩

  have inf_ (a b : img) :e_schlange (a ⊓ b)  = a ⊓ b  := by
    simp [inf]

  let supSet : SupSet img := ⟨fun x ↦ e_schlange (sSup x)⟩
  let infSet : InfSet img := ⟨fun x ↦ e_schlange (sInf x)⟩
  let top : Top img := ⟨e_schlange ⊤⟩
  let bot : Bot img := ⟨e_schlange ⊥⟩

  have h_e (a : img) :  a = e_schlange a := by
    apply Eq.symm
    simp [img, Image, e_schlange]
    obtain ⟨val, property⟩ := a
    simp_all only [img]
    ext : 1
    simp_all only [Set.mem_setOf_eq, Set.val_codRestrict_apply]
    simp_all only [img]
    exact property

  have e_schlange_monotone : Monotone e_schlange := by
      simp only [Monotone, Set.codRestrict, Subtype.mk_le_mk, e_schlange]
      exact fun ⦃a b⦄ a_1 => OrderHomClass.GCongr.mono n a_1

  have aux1 : ∀ (a b : ↑img), a ≤ a ⊔ b := by
    intro a b
    simp [sup]
    have h_2 (c d : E) : c ≤ c ⊔ d := by exact SemilatticeSup.le_sup_left c d
    let h3 := h_2 a b

    let h8 := le_of_eq (h_e a)
    apply_fun (e_schlange) at h3
    apply le_trans h8 h3
    exact e_schlange_monotone

  have sup_comm : ∀ (a b : ↑img), a ⊔ b = b ⊔ a := by
    intro a b
    simp only [sup]
    rw [sup_comm]


  have aux2 : ∀ (a b : ↑img), b ≤ a ⊔ b := by
    intro a b
    rw [sup_comm]
    apply aux1


  have aux3 : ∀ (a b c : ↑img), a ≤ c → b ≤ c → a ⊔ b ≤ c := by
    intro a b c h1 h2
    simp [sup]
    let h3 := sup_le h1 h2
    rw [h_e c]
    apply_fun e_schlange at h3
    exact h3
    exact e_schlange_monotone

  have aux4 : ∀ (a b : ↑img), a ⊓ b ≤ a := by
    intro a b
    simp [inf]
    have h_2 (c d : E) : c ⊓ d ≤ c := by exact inf_le_left
    let h3 := h_2 a b

    let h8 := le_of_eq (h_e a)
    apply_fun (e_schlange) at h3
    apply le_trans h3
    rw [← h_e]
    exact e_schlange_monotone

  have inf_comm : ∀ (a b : ↑img), a ⊓ b = b ⊓ a := by
    intro a b
    simp only [inf]
    rw [inf_comm]


  have aux5 : ∀ (a b : ↑img), a ⊓ b ≤ b := by
    intro a b
    rw [inf_comm]
    apply aux4

  have aux6 : ∀ (a b c : ↑img), a ≤ b → a ≤ c → a ≤ b ⊓ c := by
    intro a b c h1 h2
    simp [inf]
    let h3 := le_inf h1 h2
    rw [h_e c]
    apply_fun e_schlange at h3
    rw [← h_e]
    rw [← h_e] at h3
    exact h3
    exact e_schlange_monotone

  have aux7 : ∀ (s : Set ↑img), ∀ a ∈ s, a ≤ sSup s := by
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

  have aux8 : ∀ (s : Set ↑img) (a : ↑img), (∀ b ∈ s, b ≤ a) → sSup s ≤ a := by
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

  have aux9 : ∀ (s : Set ↑img), ∀ a ∈ s, sInf s ≤ a := by
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


  have aux10 : ∀ (s : Set ↑img) (a : ↑img), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
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


  have aux11 : ∀ (x : ↑img), x ≤ ⊤ := by
    simp only [Subtype.forall]
    intro a h
    simp [top]
    have h1 : a ≤ ⊤ := by
      exact OrderTop.le_top a
    apply_fun e_schlange at h1
    rw [h_e ⟨a, h⟩]
    apply h1
    exact e_schlange_monotone

  have aux12 : ∀ (x : ↑img), ⊥ ≤ x := by
    simp only [Subtype.forall]
    intro a h
    simp [bot]
    have h1 : ⊥ ≤ a := by
        exact OrderBot.bot_le a
    apply_fun e_schlange at h1
    rw [h_e ⟨a, h⟩]
    apply h1
    exact e_schlange_monotone


  have h1 (a b : ↑img) : (a : E) ⊓ (b : E) = a ⊓ b:= by
    have h2 : (a : E) ⊓ (b : E) ∈ img := by
      simp only [Image, Set.mem_setOf_eq, img]
      rw [h_e a,h_e b]
      simp [e_schlange, Nucleus.idempotent]
    simp [img, Image] at h2
    simp [inf, e_schlange, h2]
  have h_test (s : Set ↑img) : ↑(sSup s) ∈ img := by
    exact Subtype.coe_prop (sSup s)



  let semilatticesup : SemilatticeSup img := ⟨sup.max, aux1, aux2, aux3⟩
  let lattice : Lattice img := ⟨inf.min, aux4, aux5, aux6⟩
  let completelattice : CompleteLattice img := ⟨aux7, aux8, aux9, aux10, aux11, aux12⟩


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

  have leroy_aux1 : ∀ (a : ↑img) (s : Set ↑img), a ⊓ sSup s = e_schlange (a ⊓ sSup s) := by
    intro a s
    simp [supSet]
    rewrite [h_e a]
    rw [e_schlange_preserves_inf]
    rw [e_schlange_idempotent]

  have h_e_image (s : Set E) :∀ x, x ∈ img -> e_schlange x = x := by
    intro x h
    simp [e_schlange]
    exact h

  have h_e_image1 (x : E) : x ∈ img -> e_schlange ↑x = x := by
    exact fun a => h_e_image img x (h_e_image img x a)

  have h_e_image2 (x : ↑img) : e_schlange x = x := by
    exact Eq.symm (SetCoe.ext (congrArg Subtype.val (h_e x)))

  have h_e_image3 (x : E) : (h : x ∈ img) -> e_schlange x = ⟨x, h⟩ := by
    exact fun h => SetCoe.ext (h_e_image img x (h_e_image img x h))


  have aux13 : ∀ (a : ↑img) (s : Set ↑img), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
    intro a s
    rw [leroy_aux1]
    rw [inf_sSup_eq]
    simp [iSup, inf, sSup]

    have a_inf_b_mem : ∀ (b : ↑img), ↑a ⊓ ↑b ∈ img := by
      intro b
      simp [img, Image]
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
        have h_eq : a1 = ↑(⟨a1, ha1⟩ : img) := by
          rfl
        have h : ↑a ⊓ a1 ∈ img := by
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
        exact h_e_image3 (↑a ⊓ ↑(⟨a1, ha1⟩ : img)) ((Iff.of_eq (Eq.refl (↑a ⊓ a1 ∈ img))).mpr h)
        exact
          h_e_image img (↑(a ⊓ ⟨a1, ha1⟩))
            (h_e_image1 (↑(a ⊓ ⟨a1, ha1⟩)) (congrArg n (a_inf_b_mem ⟨a1, ha1⟩)))

    apply_fun e_schlange at h14
    exact h14
    exact e_schlange_monotone

  let frame : Order.Frame ↑(Image n) := Order.Frame.ofMinimalAxioms ⟨aux13⟩
  exact frame

instance inst_frame (n : Nucleus E): Order.Frame (Image n) := image_frame n

def Nucleus.frameHom (n : Nucleus E) : FrameHom E (Image n) := by
  let img := Image n

  let e_schlange : E → img := Set.codRestrict n img (by intro x; simp [img, Image]; apply n.idempotent)

  let embedding : img → E := fun x ↦ x

  let sup : Max img := ⟨fun x y ↦ e_schlange (x ⊔ y)⟩
  let inf : Min img := ⟨fun x y ↦ e_schlange (x ⊓ y)⟩

  have inf_ (a b : img) :e_schlange (a ⊓ b)  = a ⊓ b  := by
    simp [inf]

  let supSet : SupSet img := ⟨fun x ↦ e_schlange (sSup x)⟩
  let infSet : InfSet img := ⟨fun x ↦ e_schlange (sInf x)⟩
  let top : Top img := ⟨e_schlange ⊤⟩
  let bot : Bot img := ⟨e_schlange ⊥⟩

  have h_e (a : img) :  a = e_schlange a := by
    apply Eq.symm
    simp [img, Image, e_schlange]
    obtain ⟨val, property⟩ := a
    simp_all only [img]
    ext : 1
    simp_all only [Set.mem_setOf_eq, Set.val_codRestrict_apply]
    simp_all only [img]
    exact property

  have e_schlange_monotone : Monotone e_schlange := by
      simp only [Monotone, Set.codRestrict, Subtype.mk_le_mk, e_schlange]
      exact fun ⦃a b⦄ a_1 => OrderHomClass.GCongr.mono n a_1
  have h1 (a b : ↑img) : (a : E) ⊓ (b : E) = a ⊓ b:= by
    have h2 : (a : E) ⊓ (b : E) ∈ img := by
      simp only [Image, Set.mem_setOf_eq, img]
      rw [h_e a,h_e b]
      simp [e_schlange, n.idempotent]
    simp [img, Image] at h2
    simp [inf, e_schlange, h2]

  have h_test (s : Set ↑img) : ↑(sSup s) ∈ img := by
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

  let imgtype := ↑img
  exact ⟨⟨⟨e_schlange, e_schlange_preserves_inf⟩, (by simp[e_schlange,inst_frame];exact rfl)⟩, aux43⟩

def f_untenstern (f : FrameHom X Y) := fun y : Y ↦ sSup {w : X | f w ≤ y}

lemma Nucleus.gc (n : Nucleus E) : GaloisConnection (n.frameHom) (f_untenstern n.frameHom) := by
  simp [GaloisConnection,f_untenstern, Nucleus.frameHom]
  intro a a_1 b
  apply Iff.intro
  · intro a_2
    simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq]
    intro c h1
    apply h1
    exact a_2
  · intro a_2
    simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq] at a_2
    refine Subtype.coe_le_coe.mp ?_
    simp only [Set.val_codRestrict_apply]
    simp [Image] at b
    rw [← b]
    apply n.monotone
    apply a_2
    intro c h
    rw [← Subtype.coe_le_coe] at h
    simp only [Set.val_codRestrict_apply] at h
    apply le_trans n.le_apply h

lemma Nucleus.gc' (n : Nucleus E) : GaloisConnection (n.frameHom) (Subtype.val) := by
  intro a b
  apply Iff.intro
  . intro h
    simp_rw [← Subtype.coe_le_coe, Nucleus.frameHom] at h
    simp at h
    apply le_trans n.le_apply h
  . intro h
    rw [← Subtype.coe_le_coe, Nucleus.frameHom]
    simp
    have h_help : ↑b = n ↑b := by
      simp [Image] at b
      obtain ⟨val, property⟩ := b
      simp_all only
    rw [h_help]
    exact n.monotone h

lemma f_untenstern_eq_val (n : Nucleus E) : (f_untenstern n.frameHom) = Subtype.val := by
  ext i
  exact GaloisConnection.u_unique n.gc n.gc' (by simp)


/-
def Nucleus.eq_f_obenstern_f_untenstern (n : Nucleus E) : n = ((f_obenstern n.frameHom) ⋙ (f_untenstern n.frameHom)).obj := by
  ext x
  simp only [f_obenstern, frameHom, FrameHom.coe_mk, InfTopHom.coe_mk, InfHom.coe_mk, f_untenstern,
    Functor.comp_obj]
  apply le_antisymm
  . apply le_sSup
    simp only [Set.mem_setOf_eq]
    have h : ∀ a b : (Image n), (a : E) ≤ (b : E) → a ≤ b := by
      simp only [Subtype.coe_le_coe, imp_self, implies_true]
    apply h
    simp only [Set.val_codRestrict_apply]
    rw [Nucleus.idempotent]

  . apply sSup_le
    simp
    intro b h
    apply_fun (fun (x : Image n) ↦ (x : E)) at h
    simp at h
    have h1: b ≤ n b := by
      exact n.le_apply
    exact Preorder.le_trans b (n b) (n x) h1 h
    exact fun ⦃a b⦄ a => a

def Nucleus.frameHom_Leroy_Embedding (n : Nucleus E) : Leroy_Embedding n.frameHom := by
  have h : Function.Surjective (f_obenstern n.frameHom).obj := by
    simp [Function.Surjective, frameHom]
    intro a h
    simp [Image] at h
    use a
    simp [f_obenstern]
    exact SetCoe.ext h
  refine { comp_id := ?_ }
  exact f_surjective_one n.frameHom h


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
-/
