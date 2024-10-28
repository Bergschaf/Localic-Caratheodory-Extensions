import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Topology.Defs.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Sets.Opens
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.ContinuousMap.Defs


open CategoryTheory

universe u
/-
variable (X Y : Type*) [Order.Frame X][Order.Frame Y][TopologicalSpace X][TopologicalSpace Y]


--def O (x : Type u)[TopologicalSpace x] : Type := by sorry

/--/
instance O (x : Type*) [Order.Frame x] : Category x where
  Hom A B := PLift (A ≤ B)
  id A := ⟨(by exact Preorder.le_refl A)⟩
  comp f g := ⟨(by  simp at f; simp at g; apply (Preorder.le_trans); apply f.down; apply g.down)⟩




noncomputable def fstern (f: X -> Y)(h : Continuous f): CategoryTheory.Functor Y X :=
  ⟨⟨f.invFun, (by intro y x finv;apply CategoryTheory.homOfLE;)⟩ , sorry, sorry⟩
--/
---------------------------v des darf ich, oder????
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
--- Geschweifte klammern sind wichtig

/-instance test (x : Type*)[TopologicalSpace x] : Category (TopologicalSpace.Opens x) where
  Hom A B := PLift (A.carrier ⊆ B.carrier)
  id A := ⟨(by rfl)⟩
  comp f g := ⟨subset_trans f.down g.down⟩-/

abbrev O := TopologicalSpace.Opens -- TODO das ist wahrscheinlich Falsch


--abbrev fstar := TopologicalSpace.Opens.comap



def Opens_map (f : C(X, Y)) : FrameHom (O X) (O Y) where
  toFun x := sSup {y : O Y | TopologicalSpace.Opens.comap f y ≤ x}
  map_inf' a b := sorry -- (by simp; ext x; apply Iff.intro; simp; intro y h1 h2 h3; apply And.intro; use y; use y; intro h; simp; use (sSup {y | (TopologicalSpace.Opens.comap f) y ≤ a} ⊓ sSup {y | (TopologicalSpace.Opens.comap f) y ≤ b}); simp; apply And.intro; apply And.intro; refine     inf_le_of_left_le ?h.left.left.h; simp; refine inf_le_of_right_le ?h.left.right.h; simp; exact h)
  map_top' := (by simp)
  map_sSup' s := (by simp_all; ext x1; apply Iff.intro; sorry; sorry)


theorem Opens_map_mono (f : C(X,Y)) {s t : O X} (h : s ≤ t) : Opens_map f s ≤ Opens_map f t :=
  OrderHomClass.mono (Opens_map f) h


#check Opens_map (sorry : C(X,Y))
#check TopologicalSpace.Opens.comap (sorry : C(X,Y))

-- TopologicalSpace.Opens.map???
def f_obenstern (f : C(X, Y)) : O Y ⥤ O X where
  obj := TopologicalSpace.Opens.comap f
  map := (by intro x y; intro h; apply homOfLE; apply TopologicalSpace.Opens.comap_mono; exact leOfHom h)

def f_untenstern (f : C(X, Y)) : O X ⥤ O Y where
  obj :=  (Opens_map f)
  map := (by intro x y h; apply homOfLE; apply Opens_map_mono; exact leOfHom h)


def f_adj (f : C(X, Y)) : Adjunction (f_obenstern f) (f_untenstern f) where
  unit := sorry
  counit := sorry
