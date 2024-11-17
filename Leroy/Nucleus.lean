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



lemma nucleus_equiv_subframe (e : E ⥤ E) :(∃  n : Nucleus e,true) → (∃ (X : Type u),∃ h : Order.Frame X, ∃ f : FrameHom E X, e =(f_obenstern f) ⋙ (f_untenstern f) ∧ ∃ k : Leroy_Embedding f, true)  := by
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
    sorry
  let semilatticesup : SemilatticeSup img := ⟨aux1, aux2, aux3⟩
  let lattice : Lattice img := ⟨aux4, aux5, aux6⟩
  let completelattice : CompleteLattice img := ⟨aux7, aux8, aux9, sorry, sorry, sorry⟩
  let frame : Order.Frame img := Order.Frame.ofMinimalAxioms ⟨(by sorry)⟩

  have h1 (a b : img) : (a : E) ⊓ (b : E) = a ⊓ b:= by
    have h2 : (a : E) ⊓ (b : E) ∈ img := by
      simp only [Image, Set.mem_setOf_eq, img]
      rw [h_e a,h_e b]
      rw [n.preserves_inf]
      simp only [Set.val_codRestrict_apply, e_schlange]
      repeat rw [n.idempotent]
    simp [img, Image] at h2
    simp [inf, e_schlange, h2]

  have aux42 : ∀ (a b : E), e_schlange (a ⊓ b) = e_schlange a ⊓ e_schlange b := by
    intro a b
    let h2 := n.preserves_inf a b
    have h3 : e_schlange (a ⊓ b) = e.obj (a ⊓ b) := by
      simp [e_schlange]
    let h4 := Eq.trans h3 h2
    let h5 := h1 (e_schlange a) (e_schlange b)
    let h6 := Eq.trans h4 h5
    exact SetCoe.ext h6

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

  let frameHom : FrameHom E imgtype := ⟨⟨⟨e_schlange, aux42⟩, (by simp[e_schlange,top];exact rfl)⟩, aux43⟩
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
