import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Sets.Opens
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Data.Real.Basic

open CategoryTheory

variable {X Y E: Type*} [Order.Frame X] [Order.Frame Y] [Order.Frame E]
--- Geschweifte klammern sind wichtig
variable {Top_X Top_Y : Type*} [TopologicalSpace Top_X] [TopologicalSpace Top_Y]

abbrev O := TopologicalSpace.Opens

def comap (f : C(Top_X, Top_Y)) := TopologicalSpace.Opens.comap f

def f_obenstern_top (f : C(Top_X, Top_Y)) : O Top_Y ⥤ O Top_X where
  obj := TopologicalSpace.Opens.comap f
  map := (by intro x y; intro h; apply homOfLE; apply TopologicalSpace.Opens.comap_mono; exact leOfHom h)

/-
def ball := Metric.ball (1 : Real) 1

def ball2 := Metric.ball (0 : Real) 1

def funktion (x : ball) : ball := x

def f_continuous : C(ball, ball) := ⟨funktion, (by exact { isOpen_preimage := fun s a => a })⟩

#check (f_adj f_continuous).left_triangle_components-/
