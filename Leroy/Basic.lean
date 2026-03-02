import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic.ApplyFun

open CategoryTheory

variable {X Y E: Type*} [Order.Frame X] [Order.Frame Y] [Order.Frame E]
--- Geschweifte klammern sind wichtig

def frameHom_monotone (f : FrameHom Y X) : {X_1 Y_1 : Y} → (X_1 ⟶ Y_1) → ((fun x => f x) X_1 ⟶ (fun x => f x) Y_1) := by
  intro x y h
  simp
  apply homOfLE
  have h1 := leOfHom h
  gcongr

def f_obenstern (f : FrameHom Y X) : Y ⥤ X where
  obj x := f x
  map := frameHom_monotone f

lemma f_obenstern_eq_f (f : FrameHom X Y): (f_obenstern f).obj = f := by
  rfl

def f_untenstern_map (f_o: FrameHom Y X) : {X_1 Y_1 : X} → (X_1 ⟶ Y_1) → (sSup {y | f_o y ≤ X_1} ⟶ sSup {y | f_o y ≤ Y_1}) := by
  intro x1 x2 h
  apply homOfLE
  simp_all
  intro z h1
  let h2 := leOfHom h
  apply le_sSup
  simp
  apply le_trans h1 h2

def f_untenstern (f_o: FrameHom Y X) : X ⥤ Y where -- TODO nicht als Funktor sondern als GloisConection
  obj x := sSup {y : Y | f_o y ≤ x} -- kommutiert mit endlichen vereinigungen und unendlichen schnitten wegen adjunktion
  map := f_untenstern_map f_o

def f_untenstern.mono (f_o: FrameHom Y X) : Monotone (f_untenstern f_o).obj := by
  simp [Monotone, f_untenstern, le_sSup_iff, upperBounds]
  intro a b h c h1 d h2
  exact h1 (le_trans h2 h)

def ig_obenstern (i : FrameHom E X) (g : FrameHom X Y) : (f_obenstern i) ⋙ (f_obenstern g) = (f_obenstern (FrameHom.comp g i)) := by
  rfl

def ig_untenstern (i : FrameHom E X) (g : FrameHom X Y) :  (f_untenstern i).obj  ∘ (f_untenstern g).obj = (f_untenstern (FrameHom.comp g i)).obj := by
  simp [f_untenstern]
  rw [Function.comp_def]
  have h3:∀ x : Y,  sSup {y | i y ≤ sSup {y | g y ≤ x}} = sSup {y | g (i y) ≤ x} := by
    intro x
    apply le_antisymm_iff.mpr
    apply And.intro
    . simp
      intro b h
      apply le_sSup
      simp
      have h1 : g  (sSup {y | g y ≤ x}) ≤ x := by
        simp [g.map_sSup']
      let h2 := frameHom_monotone g (homOfLE h)
      let h2 := leOfHom h2
      exact Preorder.le_trans (g (i b)) ((fun x => g x) (sSup {y | g y ≤ x})) x h2 h1

    . simp
      intro b h
      simp [le_sSup, h]

  exact
    (Set.eqOn_univ (fun x => sSup {y | i y ≤ sSup {y | g y ≤ x}}) fun x =>
          sSup {y | g (i y) ≤ x}).mp
      fun ⦃x⦄ a => h3 x




def f_unit (f : FrameHom Y X) : PLift ((𝟭 Y).obj x ≤ (f_obenstern f ⋙ f_untenstern f).obj x):= by
  simp
  refine { down := ?down }
  simp [f_untenstern, f_obenstern]
  apply le_sSup
  simp


def f_counit (f: FrameHom Y X) : PLift ((f_untenstern f ⋙ f_obenstern f).obj x ≤ (𝟭 X).obj x) := by
  simp
  apply PLift.up
  simp [f_obenstern, f_untenstern]

def f_adj (f : FrameHom Y X) : (f_obenstern f) ⊣ (f_untenstern f) where
  unit := {app := fun x => ⟨f_unit f⟩}
  counit := {app := fun x => ⟨f_counit f⟩}




def triangle_one_obj (f : FrameHom Y X) (y : Y): ((f_obenstern f) ⋙ (f_untenstern f) ⋙ (f_obenstern f)).obj y = (f_obenstern f).obj y := by
  let h : (f_obenstern f) ⟶ (f_obenstern f) ⋙ (f_untenstern f) ⋙ (f_obenstern f) :=
    ⟨fun x ↦ (f_obenstern f).map ((f_adj f).unit.app x), (by aesop_cat)⟩

  let h2 : (f_obenstern f) ⋙ (f_untenstern f) ⋙ (f_obenstern f) ⟶  (f_obenstern f) :=
    ⟨fun x ↦ (f_adj f).counit.app ((f_obenstern f).obj x), (by aesop_cat)⟩

  apply le_antisymm
  apply leOfHom
  exact h2.app y
  apply leOfHom
  exact h.app y

def triangle_one (f : FrameHom Y X) : ((f_obenstern f) ⋙ (f_untenstern f) ⋙ (f_obenstern f)) = (f_obenstern f) := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  exact fun X_1 => triangle_one_obj f X_1
  intro X_1 Y_1 f_1
  simp_all only [Functor.comp_obj, Functor.comp_map]
  rfl

def triangle_two_obj (f: FrameHom Y X) (x : X): ((f_untenstern f) ⋙ (f_obenstern f) ⋙ (f_untenstern f)).obj x = (f_untenstern f).obj x := by
  let f1 : (f_untenstern f) ⟶ ((f_untenstern f) ⋙ (f_obenstern f) ⋙ (f_untenstern f)):=
    ⟨fun x ↦(f_adj f).unit.app ((f_untenstern f).obj x), (by aesop_cat)⟩

  let f2 : ((f_untenstern f) ⋙ (f_obenstern f) ⋙ (f_untenstern f)) ⟶ (f_untenstern f) :=
    ⟨fun x ↦ (f_untenstern f).map ((f_adj f).counit.app x), (by aesop_cat)⟩

  apply le_antisymm
  apply leOfHom
  exact f2.app x
  apply leOfHom
  exact f1.app x


def triangle_two (f: FrameHom Y X): ((f_untenstern f) ⋙ (f_obenstern f) ⋙ (f_untenstern f)) = (f_untenstern f):= by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  exact fun X_1 => triangle_two_obj f X_1
  intro X_1 Y_1 f_1
  simp_all only [Functor.comp_obj, Functor.comp_map]
  rfl


-- Aussage 3: linksadjungierte ist fully faithfull (unit ist iso)

def f_injective_one (f: FrameHom Y X) : Function.Injective (f_untenstern f).obj → (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 ( X) := by
  intro h1
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  intro x1
  simp
  apply_fun (f_untenstern f).obj
  apply triangle_two_obj f x1
  intro X_1 Y_1 f_1
  simp_all only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
  rfl

def f_injective_surjective (f: FrameHom Y X) : Function.Injective (f_untenstern f).obj → Function.Surjective (f_obenstern f).obj := by
  intro a b
  use (f_untenstern f).obj b
  have h: (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 (X) := by
    apply f_injective_one f a

  apply_fun (fun x ↦ x.obj) at h
  rw [← @Functor.comp_obj]
  rw [h]
  simp

def f_one_surjective (f: FrameHom Y X) : (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 X → Function.Surjective (f_obenstern f).obj := by
  intro h1
  rw [Function.Surjective]
  intro a1
  use (f_untenstern f).obj a1
  rw [← @Functor.comp_obj]
  rw [h1]
  simp


def f_surjective_one (f: FrameHom Y X) : Function.Surjective (f_obenstern f).obj → (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 (X) := by
  intro h1
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  intro x1
  simp
  have h (y : Y): ((f_obenstern f) ⋙ (f_untenstern f) ⋙ (f_obenstern f)).obj y = (f_obenstern f).obj y := by
    exact triangle_one_obj f y

  simp at h
  let inv := Function.surjInv h1
  have h := h (inv x1)
  simp [inv, Function.surjInv_eq] at h
  exact h
  intro X_1 Y_1 f_1
  simp_all only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
  rfl

def f_one_injective (f: FrameHom Y X) :  (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 (X) → Function.Injective (f_untenstern f).obj := by
  intro h
  apply_fun (fun x ↦ x.obj) at h
  have h4 (x : X) : ((f_untenstern f) ⋙ (f_obenstern f)).obj x= x := by
    exact congrFun h x
  have h6 : Function.HasLeftInverse (f_untenstern f).obj :=
    ⟨(f_obenstern f).obj, (by exact h4)⟩
  exact Function.HasLeftInverse.injective h6


class Leroy_Embedding (f : FrameHom Y X) where -- Galois Insertion
  comp_id : (f_untenstern f) ⋙ (f_obenstern f) = 𝟭 X



-------
