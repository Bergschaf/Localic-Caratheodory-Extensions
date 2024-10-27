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
variable (X Y : Type u)[Nonempty X] [TopologicalSpace X] [TopologicalSpace Y]

/-instance test (x : Type*)[TopologicalSpace x] : Category (TopologicalSpace.Opens x) where
  Hom A B := PLift (A.carrier ⊆ B.carrier)
  id A := ⟨(by rfl)⟩
  comp f g := ⟨subset_trans f.down g.down⟩-/

abbrev O := TopologicalSpace.Opens -- TODO das ist wahrscheinlich Falsch


--abbrev fstar := TopologicalSpace.Opens.comap

def f_star (f : C(X, Y)) : FrameHom (O X) (O Y) where
  toFun := fun x ↦ sSup {y : O Y | TopologicalSpace.Opens.comap f y ≤ x}
  map_inf' a b := (by simp; sorry)
  map_top' := (by simp)
  map_sSup' s := (by simp_all; ext x; apply Iff.intro; intro h; simp; sorry; sorry)
