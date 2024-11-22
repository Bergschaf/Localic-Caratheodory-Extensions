import Leroy.Basic
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Hom.CompleteLattice

variable {X Y E : Type*} [Order.Frame X] [Order.Frame Y] [Order.Frame E]



lemma factorisation (i : FrameHom E X) (f : FrameHom E Y) [inst : Leroy_Embedding i] :
    (∀ v : E, (f_untenstern i).obj ((f_obenstern i).obj v)  ≤ (f_untenstern f).obj ((f_obenstern f).obj v) ) ↔
  (∃ (g : FrameHom X Y), f = FrameHom.comp g i) := by
  apply Iff.intro
  . intro h
    have h1 (v : E): (f_obenstern f).obj v =( (f_obenstern f).obj ∘ (f_untenstern i).obj ∘ (f_obenstern i).obj ) v:= by
      apply le_antisymm_iff.mpr
      apply And.intro
      . simp [f_untenstern, f_obenstern]
        apply le_sSup
        simp
        use v


      . let h2 := h v
        let h2 := CategoryTheory.homOfLE h2
        let h3 := CategoryTheory.leOfHom ((f_obenstern f).map h2)
        let tr_1 := triangle_one f
        apply_fun (fun x ↦ x.obj v) at tr_1
        simp at tr_1
        simp [tr_1] at h3
        exact h3

    let g := fun x ↦ f ((f_untenstern i).obj x)
    have i_surjective : Function.Surjective i:= by
        apply f_one_surjective i
        use (inst.comp_id)

    have h_27 : g ∘ i = f := by
      exact Eq.symm ((fun f₁ f₂ => (Set.eqOn_univ f₁ f₂).mp) (⇑f) (g ∘ ⇑i) fun ⦃x⦄ a => h1 x)


    have aux1 :∀ (a b : X), g (a ⊓ b) = g a ⊓ g b:= by
      intro a b
      let h := i_surjective
      rw [Function.Surjective] at h
      let h42 := h b
      rcases h42 with ⟨c, h42⟩
      let h43 := h a
      rcases h43 with ⟨d, h43⟩
      rw [← h43, ← h42]
      let h_28 := h_27
      apply_fun (fun x ↦ (x (d ⊓ c))) at h_28
      simp at h_28
      let h_29 := h_27
      let h_30 := h_27
      apply_fun (fun x ↦ (x (d))) at h_29
      apply_fun (fun x ↦ (x (c))) at h_30
      simp at h_29
      simp at h_30
      rw [h_28,h_29,h_30]

    have aux2 : g ⊤ = ⊤ := by
      have h0 : i ⊤ = ⊤ := by simp
      apply_fun (g .) at h0
      have h_28 := h_27
      apply_fun (fun x ↦ (x (⊤))) at h_28
      simp at h_28
      exact h_28

    have aux3 : ∀ (s : Set X), g (sSup s) = sSup ((fun a => g a) '' s) := by
      intro s
      let h := i_surjective
      rw [Function.Surjective] at h

      let h45 := Set.preimage i s
      have h46 : i '' h45 = s := by
        exact Set.image_preimage_eq s i_surjective

      let c := sSup h45
      let h42 : i c = sSup s := by
        simp [c, h46]

      rw [← h46]
      rw [← Set.image_comp]
      have h47 : (fun a ↦ g a) ∘ i = f := by
        exact h_27
      rw [h47]
      let h_28 := h_27
      apply_fun (fun x ↦ (x (c))) at h_28
      simp at h_28

      let h_29 := h_27
      apply_fun (fun x ↦ (x (sSup h45))) at h_29
      simp at h_29
      rw [h_29]

    use ⟨⟨⟨g, aux1⟩, aux2⟩, aux3⟩

    exact FrameHom.ext h1

  . intro h
    rcases h with ⟨g,h⟩
    intro v
    let h0 := ig_untenstern i g
    rw [←h] at h0
    let h_minuseins := ig_obenstern i g
    rw [← h] at h_minuseins
    have h_minus2 : (f_untenstern f).obj ∘ (f_obenstern f).obj = ((f_untenstern i).obj ∘ (f_untenstern g).obj ∘ (f_obenstern g).obj ∘ (f_obenstern i).obj) := by
      rw [← h0]
      rw [← h_minuseins]
      rfl
    have h2  : v ≤ ((f_untenstern i).obj ∘ (f_untenstern g).obj ∘ (f_obenstern g).obj ∘ (f_obenstern i).obj) v := by
      rw [← h_minus2]
      simp [f_untenstern, f_obenstern]
      apply le_sSup
      simp
    let h3 := CategoryTheory.homOfLE h2
    let h4 := (f_adj i).homEquiv v (((f_untenstern g).obj ∘ (f_obenstern g).obj ∘ (f_obenstern i).obj) v)

    let h5 := h4.invFun h3
    let h6 := (f_untenstern i).map h5
    let h7 := CategoryTheory.leOfHom h6

    let h_minus3 := h_minus2
    apply_fun (fun x ↦ x v) at h_minus3
    simp at h7
    simp at h_minus3
    rw [← h_minus3] at h7
    exact h7
