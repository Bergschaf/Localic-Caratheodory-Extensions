import Leroy.Basic
import Mathlib.Topology.ContinuousMap.Defs


variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

def factorisation (i : C(X, E)) (f : C(Y, E)) [Leroy_Embedding i] :
    ∀ v : O E, (f_untenstern i).obj ((f_obenstern i).obj v)  ≤ (f_untenstern f).obj ((f_obenstern f).obj v)  →
  (∃ (g : C(Y, X)), ∀ y : Y, f y = i (g y)) := by
  intro v h
