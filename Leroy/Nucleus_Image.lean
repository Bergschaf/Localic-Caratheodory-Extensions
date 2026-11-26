module

public import Leroy.Nucleus
public import Mathlib.Order.Sublocale

/-!
# Images of nuclei

The range of a nucleus as a frame in its own right, along with the canonical frame homomorphism
into it and the Galois connection it induces.
-/

@[expose] public section

variable {X Y E : Type*} [Order.Frame X] [Order.Frame E] [Order.Frame Y]

/-- The image of a nucleus, represented by the range of its closure operator. -/
def Image (e : Nucleus X) : Set X := Set.range e

/-- A nucleus is coerced to its image. -/
instance : Coe (Nucleus X) (Set X) where
  coe := Image

/-- Membership in the image of a nucleus is exactly being a fixed point of the nucleus. -/
@[simp] theorem mem_Image (e : Nucleus X) {x : X} :
    x ∈ Image e ↔ e x = x := by
  exact Nucleus.mem_range

/-- The image of a nucleus is closed under implication, hence a sub-Heyting-algebra of the frame. -/
lemma Image_himp_closed (n : Nucleus E) (a b : E)
    (ha : a ∈ Image n) (hb : b ∈ Image n) : a ⇨ b ∈ Image n := by
  have ha' := (mem_Image n).mp ha
  have hb' := (mem_Image n).mp hb
  apply (mem_Image n).2
  apply le_antisymm
  · apply le_himp_iff.mpr
    calc
      n (a ⇨ b) ⊓ a ≤ n (a ⇨ b) ⊓ n a := inf_le_inf_left _ (by rw [ha'])
      _ = n ((a ⇨ b) ⊓ a) := (n.map_inf' _ _).symm
      _ ≤ n b := n.monotone (le_himp_iff.mp le_rfl)
      _ = b := hb'
  · exact n.le_apply

/-- The image of a nucleus carries a frame structure inherited from the ambient frame. -/
instance image_frame (n : Nucleus E) : Order.Frame (Image n) := by
  change Order.Frame (n.toSublocale)
  exact Sublocale.carrier.instFrame

namespace Nucleus

/-- The canonical frame hom from a frame to the range of a nucleus. -/
def frameHom (n : Nucleus E) : FrameHom E (Image n) := by
  change FrameHom E (n.toSublocale)
  exact n.toSublocale.restrict

/-- Evaluating the canonical frame homomorphism of a nucleus computes the nucleus. -/
@[simp] lemma frameHom_apply_val (n : Nucleus E) (x : E) :
    (n.frameHom x : E) = n x := by
  change (n.toSublocale.restrict x : E) = n x
  rw [Nucleus.restrict_toSublocale]

/-- The canonical frame homomorphism into a nucleus's image preserves implication. -/
lemma frameHom_map_himp (n : Nucleus E) (a b : Image n) :
    n.frameHom ((a : E) ⇨ (b : E)) = a ⇨ b := by
  apply Subtype.ext
  calc
    (n.frameHom ((a : E) ⇨ (b : E)) : E) = n ((a : E) ⇨ (b : E)) :=
      frameHom_apply_val n _
    _ = (a : E) ⇨ (b : E) :=
      (mem_Image n).mp (Image_himp_closed n _ _ a.property b.property)
    _ = (a ⇨ b : Image n) := by
      symm
      exact Sublocale.coe_himp (S := n.toSublocale) a b

end Nucleus

/-- The right adjoint associated to a frame hom. -/
def lowerStar (f : FrameHom X Y) : Y → X :=
  fun y ↦ sSup {x | f x ≤ y}

/-- The canonical frame homomorphism of a nucleus is a Galois connection with the coercion
of the image back into the frame. -/
lemma Nucleus.gc' (n : Nucleus E) :
    GaloisConnection n.frameHom (Subtype.val) := by
  change GaloisConnection n.toSublocale.restrict Subtype.val
  exact n.toSublocale.giRestrict.gc

/-- For a nucleus closure, the right adjoint of the canonical homomorphism is just coercion
out of the image. -/
lemma lowerStar_eq_val (n : Nucleus E) :
    lowerStar n.frameHom = Subtype.val := by
  funext y
  change sSup {x : E | n.toSublocale.restrict x ≤ y} = (y : E)
  apply le_antisymm
  · apply sSup_le
    intro x hx
    exact (n.toSublocale.giRestrict.gc x y).mp hx
  · apply le_sSup
    exact (n.toSublocale.giRestrict.gc y y).mpr le_rfl

/-- The canonical homomorphism into a nucleus image forms a Galois connection with the induced
lower-star map: the embedding is a Galois insertion. -/
lemma Nucleus.gc (n : Nucleus E) :
    GaloisConnection n.frameHom (lowerStar n.frameHom) := by
  rw [lowerStar_eq_val]
  exact n.gc'
