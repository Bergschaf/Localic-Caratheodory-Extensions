import Leroy.Basic
import Mathlib.Topology.Bases
open CategoryTheory

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

class Nucleus (e : X ⥤ X) where
  idempotent (x : X) : e.obj (e.obj x) = e.obj x
  increasing (x : X) : x ⟶ e.obj x
  preserves_inf (x y : X) : e.obj (x ⊓ y) = e.obj x ⊓ e.obj y


def Image (e : X ⥤ X) [Nucleus e] : Set (X) :=
  {v : X | e.obj v = v}

--lemma nucleus_properties (e : O E ⥤ O E) [Nucleus e] : ∃ (X : Type*),∃ (h : TopologicalSpace X), ∃ f : C(X, E), e = (f_obenstern f) ⋙ (f_untenstern f) := by
--  let img  := {v : (O E) // e.obj v = v}
--  let top : TopologicalSpace.IsTopologicalBasis img := by sorry


  -- make the open sets -> topological basis -> generate topological space

structure Subframe (X : Type*) [Order.Frame X] where
  e : X ⥤ X
  nucleus : Nucleus e

-- Leroy CH 3
instance : LE (Subframe X) where
  le x y := ∀ v : X, y.e.obj v ≤ x.e.obj v



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
