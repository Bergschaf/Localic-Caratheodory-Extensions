module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Tactic.ApplyFun

/-!
# The upper-star / lower-star adjunction between frames

Given a frame homomorphism `f : Y → X`, we construct the direct image functor
`upperStar` (upper star) from `Y` to `X` and its right adjoint `lowerStar`
(lower star) sending an element back to the supremum of the preimage, together
with the unit and counit of the adjunction and their triangular identities.
This adjunction is the categorical backbone of the sublocale development.

Reference: Leroy's thesis on localic measure theory.
-/

@[expose] public section

open CategoryTheory

variable {X Y E : Type*} [Order.Frame X] [Order.Frame Y] [Order.Frame E]
-- (Curly braces matter here: they keep the arguments implicit.)

/-- A frame homomorphism is monotone: the action on morphisms of the preorder-category of frames
induced by the pointwise application of `f`. -/
def frameHom_monotone (f : FrameHom Y X) : {X_1 Y_1 : Y} → (X_1 ⟶ Y_1) →
    ((fun x => f x) X_1 ⟶ (fun x => f x) Y_1) := by
  intro x y h
  exact homOfLE (show f x ≤ f y from by
    have h1 := leOfHom h
    gcongr)
/-- The upper star of `f`: the direct image functor from `Y` to `X`, i.e. applying `f` pointwise. -/
def upperStar (f : FrameHom Y X) : Y ⥤ X where
  obj x := f x
  map := frameHom_monotone f
/-- On objects, the upper star of `f` is just `f`. -/
lemma upperStar_eq_f (f : FrameHom X Y) : (upperStar f).obj = f := by
  rfl
/-- The action on morphisms of the lower star: monotonicity of the supremum of the preimage. -/
def lowerStar_map (f_o : FrameHom Y X) : {X_1 Y_1 : X} → (X_1 ⟶ Y_1) →
    (sSup {y | f_o y ≤ X_1} ⟶ sSup {y | f_o y ≤ Y_1}) := by
  intro x1 x2 h
  apply homOfLE
  simp_all only [sSup_le_iff, Set.mem_ofPred_eq]
  intro z h1
  let h2 := leOfHom h
  apply le_sSup
  simp only [Set.mem_ofPred_eq]
  apply le_trans h1 h2

/-- The lower star of `f`: the right adjoint to the upper star, sending `x` to the supremum of the
elements of `Y` that `f` maps below `x`. The frame homomorphism property of `f` makes this commute
with finite joins and arbitrary meets. -/
-- TODO: formulate this as a Galois connection instead of a functor
def lowerStar (f_o : FrameHom Y X) : X ⥤ Y where
  -- commutes with finite joins and arbitrary meets because of the adjunction
  obj x := sSup {y : Y | f_o y ≤ x}
  map := lowerStar_map f_o
/-- The lower star is monotone. -/
theorem lowerStar.mono (f_o : FrameHom Y X) : Monotone (lowerStar f_o).obj := by
  intro a b h
  exact sSup_le_sSup fun y hy => le_trans hy h
/-- Upper stars compose: the upper star of `g ∘ i` is the composite of the upper stars. -/
theorem comp_upperStar (i : FrameHom E X) (g : FrameHom X Y) :
    (upperStar i) ⋙ (upperStar g) = (upperStar (FrameHom.comp g i)) := by
  rfl
/-- Lower stars compose contravariantly: the lower star of `g ∘ i` is the composite of the
lower star of `i` after the lower star of `g`. -/
theorem comp_lowerStar (i : FrameHom E X) (g : FrameHom X Y) :
    (lowerStar i).obj ∘ (lowerStar g).obj = (lowerStar (FrameHom.comp g i)).obj := by
  simp only [lowerStar]
  rw [Function.comp_def]
  have h3:∀ x : Y,  sSup {y | i y ≤ sSup {y | g y ≤ x}} = sSup {y | g (i y) ≤ x} := by
    intro x
    apply le_antisymm_iff.mpr
    apply And.intro
    · apply sSup_le
      intro b h
      have h1 : g (sSup {y | g y ≤ x}) ≤ x := by
        simp
      apply le_sSup
      exact le_trans (leOfHom (frameHom_monotone g (homOfLE h))) h1
    · apply sSup_le
      intro b h
      apply le_sSup
      exact le_sSup (show i b ∈ {y : X | g y ≤ x} from h)
  exact
    (Set.eqOn_univ (fun x => sSup {y | i y ≤ sSup {y | g y ≤ x}}) fun x =>
          sSup {y | g (i y) ≤ x}).mp
      fun ⦃x⦄ a => h3 x
/-- The unit of the upper-star/lower-star adjunction at any point of `Y`. -/
def f_unit (f : FrameHom Y X) : PLift ((𝟭 Y).obj x ≤ (upperStar f ⋙ lowerStar f).obj x):= by
  simp only [Functor.id_obj, Functor.comp_obj]
  refine { down := ?down }
  simp only [lowerStar, upperStar]
  exact le_sSup le_rfl
/-- The counit of the upper-star/lower-star adjunction at any point of `X`. -/
def f_counit (f : FrameHom Y X) : PLift ((lowerStar f ⋙ upperStar f).obj x ≤ (𝟭 X).obj x) := by
  simp only [Functor.comp_obj, Functor.id_obj]
  apply PLift.up
  simp [upperStar, lowerStar]
/-- The upper star is left adjoint to the lower star. -/
def f_adj (f : FrameHom Y X) : (upperStar f) ⊣ (lowerStar f) where
  unit := {app := fun x => ⟨f_unit f⟩}
  counit := {app := fun x => ⟨f_counit f⟩}
/-- First triangular identity, on objects: the composite of the upper star with the full round
trip through the lower star is pointwise the upper star. -/
theorem triangle_one_obj (f : FrameHom Y X) (y : Y) :
    ((upperStar f) ⋙ (lowerStar f) ⋙ (upperStar f)).obj y = (upperStar f).obj y := by
  let h : (upperStar f) ⟶ (upperStar f) ⋙ (lowerStar f) ⋙ (upperStar f) :=
    ⟨fun x ↦ (upperStar f).map ((f_adj f).unit.app x), (by aesop_cat)⟩
  let h2 : (upperStar f) ⋙ (lowerStar f) ⋙ (upperStar f) ⟶  (upperStar f) :=
    ⟨fun x ↦ (f_adj f).counit.app ((upperStar f).obj x), (by aesop_cat)⟩
  apply le_antisymm
  · apply leOfHom
    exact h2.app y
  · apply leOfHom
    exact h.app y
/-- First triangular identity: the counit composed with the unit collapses the double round trip
to the identity on the upper star. -/
theorem triangle_one (f : FrameHom Y X) :
    ((upperStar f) ⋙ (lowerStar f) ⋙ (upperStar f)) = (upperStar f) := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  · exact fun X_1 => triangle_one_obj f X_1
  · intro X_1 Y_1 f_1
    simp_all only [Functor.comp_obj, Functor.comp_map]
    rfl
/-- Second triangular identity, on objects: the composite of the lower star with the full round
trip through the upper star is pointwise the lower star. -/
theorem triangle_two_obj (f : FrameHom Y X) (x : X) :
    ((lowerStar f) ⋙ (upperStar f) ⋙ (lowerStar f)).obj x = (lowerStar f).obj x := by
  let f1 : (lowerStar f) ⟶ ((lowerStar f) ⋙ (upperStar f) ⋙ (lowerStar f)):=
    ⟨fun x ↦(f_adj f).unit.app ((lowerStar f).obj x), (by aesop_cat)⟩
  let f2 : ((lowerStar f) ⋙ (upperStar f) ⋙ (lowerStar f)) ⟶ (lowerStar f) :=
    ⟨fun x ↦ (lowerStar f).map ((f_adj f).counit.app x), (by aesop_cat)⟩
  apply le_antisymm
  · apply leOfHom
    exact f2.app x
  · apply leOfHom
    exact f1.app x
/-- Second triangular identity: the unit composed with the counit collapses the double round trip
to the identity on the lower star. -/
theorem triangle_two (f : FrameHom Y X) :
    ((lowerStar f) ⋙ (upperStar f) ⋙ (lowerStar f)) = (lowerStar f) := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  · exact fun X_1 => triangle_two_obj f X_1
  · intro X_1 Y_1 f_1
    simp_all only [Functor.comp_obj, Functor.comp_map]
    rfl
-- Statement 3: a left adjoint is fully faithful iff its unit is an isomorphism

/-- If the lower star is injective on objects, the counit round trip is the identity, i.e. the
upper star exhibits a Galois insertion: injectivity of the adjoint makes the composite trivial. -/
theorem f_injective_one (f : FrameHom Y X) : Function.Injective (lowerStar f).obj →
    (lowerStar f) ⋙ (upperStar f) = 𝟭 X := by
  intro h1
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  · intro x1
    simp only [Functor.comp_obj, Functor.id_obj]
    apply_fun (lowerStar f).obj
    apply triangle_two_obj f x1
  · intro X_1 Y_1 f_1
    simp_all only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    rfl
/-- Injectivity of the lower star implies surjectivity of the upper star: a Galois insertion
is in particular an embedding onto the whole of `X`. -/
theorem f_injective_surjective (f : FrameHom Y X) : Function.Injective (lowerStar f).obj →
    Function.Surjective (upperStar f).obj := by
  intro a b
  use (lowerStar f).obj b
  have h: (lowerStar f) ⋙ (upperStar f) = 𝟭 (X) := by
    apply f_injective_one f a
  apply_fun (fun x ↦ x.obj) at h
  rw [← @Functor.comp_obj]
  rw [h]
  simp
/-- If the counit round trip is the identity, the upper star is surjective: every point of `X`
lies in the image of `f`. -/
theorem f_one_surjective (f : FrameHom Y X) : (lowerStar f) ⋙ (upperStar f) = 𝟭 X →
    Function.Surjective (upperStar f).obj := by
  intro h1
  rw [Function.Surjective]
  intro a1
  use (lowerStar f).obj a1
  rw [← @Functor.comp_obj]
  rw [h1]
  simp
/-- Surjectivity of the upper star already implies the counit round trip is the identity:
a surjective adjunction restricts to a Galois insertion. -/
theorem f_surjective_one (f : FrameHom Y X) : Function.Surjective (upperStar f).obj →
    (lowerStar f) ⋙ (upperStar f) = 𝟭 X := by
  intro h1
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  · intro x1
    simp only [Functor.comp_obj, Functor.id_obj]
    have h (y : Y) : ((upperStar f) ⋙ (lowerStar f) ⋙ (upperStar f)).obj y =
        (upperStar f).obj y := by
      exact triangle_one_obj f y
    simp only [Functor.comp_obj] at h
    let inv := Function.surjInv h1
    have h := h (inv x1)
    simp only [Function.surjInv_eq, inv] at h
    exact h
  · intro X_1 Y_1 f_1
    simp_all only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    rfl
/-- If the counit round trip is the identity, the lower star is injective on objects. -/
theorem f_one_injective (f : FrameHom Y X) : (lowerStar f) ⋙ (upperStar f) = 𝟭 X →
    Function.Injective (lowerStar f).obj := by
  intro h
  apply_fun (fun x ↦ x.obj) at h
  have h4 (x : X) : ((lowerStar f) ⋙ (upperStar f)).obj x= x := by
    exact congrFun h x
  have h6 : Function.HasLeftInverse (lowerStar f).obj :=
    ⟨(upperStar f).obj, (by exact h4)⟩
  exact Function.HasLeftInverse.injective h6
/-- A Leroy embedding is a frame homomorphism whose lower star followed by upper star is the
identity, i.e. a Galois insertion: `E` embeds into `X` as the open elements of a sublocale. -/
class Leroy_Embedding (f : FrameHom Y X) where -- Galois Insertion
  comp_id : (lowerStar f) ⋙ (upperStar f) = 𝟭 X
-------
