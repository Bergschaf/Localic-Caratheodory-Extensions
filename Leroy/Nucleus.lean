import Leroy.Basic
import Mathlib.Topology.Bases
open CategoryTheory

variable {X Y E: Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

class Nucleus (e : O X ⥤ O X) where
  idempotent (x : O X) : e.obj (e.obj x) = x
  increasing (x : O X) : x ⟶ e.obj x
  preserves_inf (x y : O X) : e.obj (x ⊓ y) = e.obj x ⊓ e.obj y


def Image (e : O X ⥤ O X) [Nucleus e] : Set (O X) :=
  {v : O X | e.obj v = v}

--- obacht leroy hat entwender E oder X vertauscht oder f_untenstern und f_obenstern
--lemma nucleus_properties (e : O E ⥤ O E) [Nucleus e] : ∃ (X : Type*),∃ (h : TopologicalSpace X), ∃ f : C(X, E), e = (f_obenstern f) ⋙ (f_untenstern f) := by
--  let img  := {v : (O E) // e.obj v = v}
--  let top : TopologicalSpace.IsTopologicalBasis img := by sorry


  -- make the open sets -> topological basis -> generate topological space

structure Subframe (X : Type*) [TopologicalSpace X] where
  e : O X ⥤ O X
  nucleus : Nucleus e

-- Leroy CH 3
instance : LE (Subframe X) where
  le x y := ∀ v : O X, y.e.obj v ≤ x.e.obj v




-- können wir Embedding einfach verwenden?
