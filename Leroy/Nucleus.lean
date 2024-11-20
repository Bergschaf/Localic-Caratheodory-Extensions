import Leroy.Basic
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice
open CategoryTheory

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

class Nucleus (e : X ⥤ X) where
  idempotent (x : X) : e.obj (e.obj x) = e.obj x
  increasing (x : X) : x ⟶ e.obj x
  preserves_inf (x y : X) : e.obj (x ⊓ y) = e.obj x ⊓ e.obj y


def Image (e : X ⥤ X) [Nucleus e] : Set X:=
  {v : X | e.obj v = v}



structure Subframe (X : Type*) [Order.Frame X] where
  e : X ⥤ X
  nucleus : Nucleus e

-- Leroy CH 3
instance : LE (Subframe X) where
  le x y := ∀ v : X, y.e.obj v ≤ x.e.obj v


lemma nucleus_equiv_subframe_1 (e : E ⥤ E ) : (∃ (X : Type u),∃ h : Order.Frame X, ∃ f : FrameHom E X, e =(f_obenstern f) ⋙ (f_untenstern f) ∧ ∃ k : Leroy_Embedding f, true) → (∃ (X : Type u),∃ h : Order.Frame X, ∃ f : FrameHom E X, e =(f_obenstern f) ⋙ (f_untenstern f)) := by
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

lemma nucleus_equiv_subframe_2 (e : E ⥤ E) : (∃ (X : Type u),∃ h : Order.Frame X, ∃ f : FrameHom E X, e =(f_obenstern f) ⋙ (f_untenstern f)) →  (∃  n : Nucleus e,true) := by
  intro h
  rcases h with ⟨X, h, f, h1⟩
  have n_1 :  ∀ (x : E), e.obj (e.obj x) = e.obj x := by
    intro x
    subst h1
    simp_all [f_untenstern, f_obenstern]
    apply le_antisymm_iff.mpr
    apply And.intro
    . apply le_sSup
      simp
      intro a h
      have h2 : sSup (⇑f '' {y | f y ≤ f x}) ≤ f x := by
        simp only [sSup_le_iff, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, imp_self, implies_true]
      exact Preorder.le_trans (f a) (sSup (⇑f '' {y | f y ≤ f x})) (f x) h h2
    . apply sSup_le_sSup
      simp
      intro a h
      have h2 : f x ≤ sSup (⇑f '' {y | f y ≤ f x}) := by
        apply le_sSup
        simp
        use x
      exact Preorder.le_trans (f a) (f x) (sSup (⇑f '' {y | f y ≤ f x})) h h2

  have n_2 : (x : E) → x ⟶ e.obj x := by
    intro x
    apply homOfLE
    subst h1
    simp [f_untenstern, f_obenstern]
    apply le_sSup
    simp only [Set.mem_setOf_eq, le_refl]

  have n_3 :  ∀ (x y : E), e.obj (x ⊓ y) = e.obj x ⊓ e.obj y := by
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
  use ⟨n_1, n_2, n_3⟩




lemma nucleus_equiv_subframe_3 (e : E ⥤ E) :(∃  n : Nucleus e,true) → (∃ (X : Type u),∃ h : Order.Frame X, ∃ f : FrameHom E X, e =(f_obenstern f) ⋙ (f_untenstern f) ∧ ∃ k : Leroy_Embedding f, true)  := by
  intro h
  rcases h with ⟨n⟩
  let img := Image e

  let e_schlange : E → img := Set.codRestrict e.obj img (by intro x; simp [img, Image]; apply n.idempotent)

  let embedding : img → E := fun x ↦ x

  let sup : Sup img := ⟨fun x y ↦ e_schlange (x ⊔ y)⟩
  let inf : Inf img := ⟨fun x y ↦ e_schlange (x ⊓ y)⟩

  have inf_ (a b : img) :e_schlange (a ⊓ b)  = a ⊓ b  := by
    simp [inf]

  let supSet : SupSet img := ⟨fun x ↦ e_schlange (sSup x)⟩
  let infSet : InfSet img := ⟨fun x ↦ e_schlange (sInf x)⟩
  let top : Top img := ⟨e_schlange ⊤⟩
  let bot : Bot img := ⟨e_schlange ⊥⟩

  have h_e (a : img) :  a = e_schlange a := by
    apply Eq.symm
    simp [img, Image, e_schlange]
    simp_all only
    obtain ⟨val, property⟩ := a
    simp_all only [img]
    ext : 1
    simp_all only [Set.mem_setOf_eq, Set.val_codRestrict_apply]
    simp_all only [img]
    exact property

  have e_schlange_monotone : Monotone e_schlange := by
      simp [e_schlange, Monotone, img, Image, Set.codRestrict]
      intro a b h
      let h5 := homOfLE h
      let h6 := e.map h5
      apply leOfHom h6


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
    simp [sSup]
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
    simp only [sSup]
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
    exact e_schlange_monotone

  have aux9 : ∀ (s : Set ↑img), ∀ a ∈ s, sInf s ≤ a := by
    intro s a h
    simp [sInf]
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
    simp only [sInf]
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
      rw [n.preserves_inf]
      simp only [Set.val_codRestrict_apply, e_schlange]
      repeat rw [n.idempotent]
    simp [img, Image] at h2
    simp [inf, e_schlange, h2]

  have h_test (s : Set ↑img) : ↑(sSup s) ∈ img := by
    exact Subtype.coe_prop (sSup s)






  let semilatticesup : SemilatticeSup img := ⟨aux1, aux2, aux3⟩
  let lattice : Lattice img := ⟨aux4, aux5, aux6⟩
  let completelattice : CompleteLattice img := ⟨aux7, aux8, aux9, aux10, aux11, aux12⟩


  have e_schlange_preserves_inf : ∀ (a b : E), e_schlange (a ⊓ b) = e_schlange a ⊓ e_schlange b := by
    intro a b
    let h2 := n.preserves_inf a b
    have h3 : e_schlange (a ⊓ b) = e.obj (a ⊓ b) := by
      simp [e_schlange]
    let h4 := Eq.trans h3 h2
    let h5 := h1 (e_schlange a) (e_schlange b)
    let h6 := Eq.trans h4 h5
    exact SetCoe.ext h6

  have h_e_bot : e.obj ⊥ = ⊥ := by
    let h1 := n.preserves_inf ⊥
    simp at h1
    apply eq_bot_of_minimal
    intro b
    have h (y : E) : ∃ x, e.obj x = y := by
      sorry
    let h := h b
    rcases h with ⟨x, h⟩
    subst h
    let h1 := h1 x
    apply not_lt_of_ge
    exact h1







  have e_schlange_idempotent : ∀ (a : E), e_schlange (e_schlange a) = e_schlange a := by
    exact fun a => Eq.symm (SetCoe.ext (congrArg Subtype.val (h_e (e_schlange a))))

  have leroy_aux1 : ∀ (a : ↑img) (s : Set ↑img), a ⊓ sSup s = e_schlange (a ⊓ sSup s) := by
    intro a s
    simp [sSup]
    rewrite [h_e a]
    rw [e_schlange_preserves_inf]
    rw [e_schlange_idempotent]

  have h_e_image (s : Set E) :∀ x, x ∈ img -> e_schlange x = x := by
    intro x h
    simp [e_schlange]
    exact h

  have h_e_image1 (x : E) : x ∈ img -> e_schlange ↑x = x := by
    exact fun a => h_e_image img x (h_e_image img x a)

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
      simp [e_schlange]
      rw [n.preserves_inf]
      rw [n.idempotent]
      rw [n.idempotent]

    have subtype_val_preserved (f : ↑img → ↑img): ( Subtype.val '' Set.range fun b ↦f b) = (Set.range fun b ↦ ↑(f b)) := by
      rw [Subtype.coe_image]
      ext x
      simp
      apply Iff.intro
      . intro h1
        rcases h1 with ⟨h21, a1, h23,h24⟩
        use a1
        use h23
        rw [h24]
      . intro h1
        rcases h1 with ⟨a1, a2,a3⟩
        have h : x ∈ img := by
          rw [← a3]
          exact Subtype.coe_prop (f ⟨a1, a2⟩)
        use h
        use a1
        use a2
        exact SetCoe.ext a3



    have h14 : ((Set.range fun b => sSup (Set.range fun (h : b ∈ Subtype.val '' s) => ↑a ⊓ b))) ≤ ((Subtype.val '' Set.range fun b => e_schlange (sSup (Subtype.val '' Set.range fun (h : b∈ s) => e_schlange (↑a ⊓ ↑b))))) := by
        rw [subtype_val_preserved]
        simp only [Set.le_eq_subset]
        rw [Set.subset_def]
        intro x h1
        simp [Set.range] at h1
        simp [Set.range]
        rcases h1 with ⟨y, h1⟩
        rw [← h1]
        -- ___ = nix (wenn y ∉ s) oder a ⊓ y (wenn y ∈ s)
        by_cases hP : ((∃ (hx : y ∈ img),true))
        . rcases hP with ⟨hx,_⟩
          use y
          use hx
          have h1_eq : (Subtype.val '' {x | ⟨y, hx⟩ ∈ s ∧ e_schlange (↑a ⊓ y) = x}) =  {x | (∃ (x : y ∈ img), ⟨y, hx⟩ ∈ s) ∧ ↑a ⊓ y = x} := by
            simp only [exists_prop]
            have a_y_mem_img : (↑a ⊓ y) ∈ img := by
              let y1 : img := ⟨y, hx⟩
              have hy1 : y1 = y := by
                rfl
              rw [← hy1]
              apply a_inf_b_mem
            rw [@Subtype.coe_image]
            simp only [Set.mem_setOf_eq, exists_and_left, exists_eq_subtype_mk_iff]
            rw [h_e_image1]
            ext x
            simp only [Set.mem_setOf_eq, and_congr_left_iff, iff_and_self]
            exact fun a a => h_e_image img y (h_e_image img y hx)
            exact a_y_mem_img

          apply_fun (fun (x : Set E) ↦ sSup x) at h1_eq
          rw [h1_eq]
          rw [h1]
          have h : x ∈ img := by
            subst x
            simp only [Image, Set.mem_setOf_eq, img]
            by_cases hP1 : ⟨y, hx⟩ ∈ s
            . apply le_antisymm_iff.mpr
              apply And.intro
              . apply le_sSup
                simp only [Set.mem_setOf_eq]
                apply And.intro
                . simp [img, Image] at hx
                  use hx
                . have h (x : E) : sSup {x} = x := by
                    exact sSup_singleton
                  have h1 : {x | (∃ (h : e.obj y = y), ⟨y, hx⟩ ∈ s) ∧ ↑a ⊓ y = x} = {↑a ⊓ y} := by
                    ext x
                    simp only [exists_prop, Set.mem_setOf_eq, Set.mem_singleton_iff]
                    apply Iff.intro
                    . intro ⟨h1, h2⟩
                      exact id (Eq.symm h2)
                    . intro h
                      apply And.intro
                      . exact ⟨h_e_image img y (h_e_image img y hx), hP1⟩
                      . exact id (Eq.symm h)
                  rw [h1]
                  rw [h]
                  have h : ↑a ⊓ y ∈ img := by
                    let y1 : img := ⟨y, hx⟩
                    have hy1 : y1 = y := by
                      rfl
                    rw [← hy1]
                    apply a_inf_b_mem
                  simp [img, Image] at h
                  exact id (Eq.symm h)

              . apply (leOfHom (n.increasing _))
            . have h : {x | (∃ (h : e.obj y = y), ⟨y, h⟩ ∈ s) ∧ ↑a ⊓ y = x} = ∅ := by
                ext x
                simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
                  forall_exists_index]
                intro x1 h1
                contradiction
              rw [h]
              simp only [sSup_empty]
              sorry


          exact h_e_image img x (h_e_image img x h)


        . use ↑(e_schlange ⊥)
          have hnull : ↑(e_schlange ⊥) ∈ img := by
            simp [e_schlange, img, Image]
            exact Nucleus.idempotent ⊥
          use hnull
          simp at hP


          have h_bot : ↑↑(e_schlange ⊥) = (⊥ : E) := by
            apply h_e_image1
            simp [img, Image]
            sorry

          have h : {x | (∃ (x : y ∈ img), ⟨y, x⟩ ∈ s) ∧ ↑a ⊓ y = x} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
                  forall_exists_index]
            intro x1 h1
            contradiction

          rw [h]
          have h1 : {x | ⟨↑(e_schlange ⊥), hnull⟩ ∈ s ∧ e_schlange (↑a ⊓ ↑(e_schlange ⊥)) = x} = ∅ := by
            ext x
            simp only [Subtype.coe_eta, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
              not_and]
            intro h
          rw [h1]
          simp [e_schlange]
          sorry



    apply_fun (fun (x : Set E) ↦ sSup x) at h14
    apply_fun e_schlange at h14
    exact h14
    exact e_schlange_monotone
    rw [Monotone]
    intro a b h
    exact sSup_le_sSup h




  let frame : Order.Frame img := Order.Frame.ofMinimalAxioms ⟨aux13⟩



  have aux43 : ∀ (s : Set E), e_schlange (sSup s) = sSup ((fun a => e_schlange a) '' s) := by
    intro s
    apply le_antisymm_iff.mpr
    apply And.intro
    . simp [sSup]
      have h0 : ∀ x ∈ s, x ≤ e_schlange x := by
        intro x h
        simp [e_schlange]
        apply (leOfHom (n.increasing x))
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
  use imgtype
  use frame

  let frameHom : FrameHom E imgtype := ⟨⟨⟨e_schlange, e_schlange_preserves_inf⟩, (by simp[e_schlange,top];exact rfl)⟩, aux43⟩
  use frameHom
  apply And.intro
  . have h : ∀ x : img, (f_untenstern frameHom).obj x = x := by
      simp [f_untenstern, frameHom, e_schlange]
      intro a h
      apply le_antisymm
      . simp
        intro b h1
        simp [img, Image] at h
        have h2 : b ≤ Set.codRestrict e.obj img (fun x => Nucleus.idempotent x : ∀ (x : E), e.obj (e.obj x) = e.obj x) b := by
          simp
          apply (leOfHom (n.increasing b))
        apply le_trans h2
        apply h1
      . apply le_sSup
        simp [img, Image] at h
        simp
        have h2 : Set.codRestrict e.obj img (fun x => Nucleus.idempotent x : ∀ (x : E), e.obj (e.obj x) = e.obj x) a = a := by
          simp [h]

        have h3 : Set.codRestrict e.obj img (fun x => Nucleus.idempotent x : ∀ (x : E), e.obj (e.obj x) = e.obj x) a = ⟨a ,h⟩ := by
          exact SetCoe.ext h

        rw [h3]
    rw [f_obenstern, f_untenstern]

    apply CategoryTheory.Functor.ext
    simp
    intro x y f
    exact rfl
    intro x
    simp
    simp [f_untenstern] at h
    let h2 := h (e.obj x)
    simp [img, Image] at h2
    apply Eq.symm
    apply h2


  . have h : Function.Surjective (f_obenstern frameHom).obj := by
      simp [Function.Surjective, frameHom]
      intro a h
      simp[imgtype,img,Image] at h
      use a
      simp [f_obenstern, e_schlange]
      exact SetCoe.ext h
    let embedding : Leroy_Embedding frameHom := ⟨f_surjective_one frameHom h⟩
    use embedding



def e_U (U : E) (H : E) : E :=
  sSup {W : E | W ⊓ U ≤ H}

lemma e_U_idempotent (U : E) (H : E) : e_U U (e_U U H) = e_U U H := by
  simp [e_U]
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply sSup_le_iff.mpr
    simp
    intro b h
    have h1 : sSup {W | W ⊓ U ≤ H} ⊓ U ≤ H := by
      simp [sSup_inf_eq]

    apply le_sSup
    simp
    apply_fun (. ⊓ U) at h
    dsimp at h
    let h3:= le_trans h h1
    simp at h3
    exact h3
    rw [Monotone]
    intro a b h
    exact inf_le_inf_right U h


  . apply sSup_le_iff.mpr
    simp
    intro b h
    apply le_sSup
    simp
    have h2 : H ≤ sSup {W | W ⊓ U ≤ H} := by
      apply le_sSup
      simp
    apply le_trans h h2

def e_U_increasing (U : E) (H : E) : H ⟶ e_U U H := by
  apply homOfLE
  simp [e_U]
  apply le_sSup
  simp


def e_U_preserves_inf (U: E) (H : E) (J : E) : e_U U (H ⊓ J) = e_U U H ⊓ e_U U J := by
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply le_inf_iff.mpr
    apply And.intro
    . simp [e_U]
      intro b h1 h2
      apply le_sSup
      simp [h1, h2]
    . simp [e_U]
      intro b h1 h2
      apply le_sSup
      simp [h1, h2]
  . simp [e_U, sSup_inf_sSup]
    intro a b h1 h2
    apply le_sSup
    simp_all only [Set.mem_setOf_eq]
    apply And.intro
    · have h3 : a ⊓ b ⊓ U ≤ a ⊓ U := by
        simp
        refine inf_le_of_left_le ?h
        exact inf_le_left
      apply le_trans h3 h1
    · have h3 : a ⊓ b ⊓ U ≤ b ⊓ U := by
        simp
        rw [inf_assoc]
        apply inf_le_of_right_le
        exact inf_le_left
      apply le_trans h3 h2

def eckig (U : E) : Subframe E :=
  ⟨⟨⟨e_U U, (by intro X Y h; simp [e_U]; apply homOfLE; simp_all only [sSup_le_iff, Set.mem_setOf_eq]; intro b a; apply le_sSup; simp [le_trans a (leOfHom h)])⟩, (by aesop_cat), (by aesop_cat)⟩, ⟨(by simp [e_U_idempotent]), (by exact fun x => e_U_increasing U x), (by exact  fun x y => e_U_preserves_inf U x y)⟩⟩
