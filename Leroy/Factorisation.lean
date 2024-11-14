import Leroy.Basic
import Mathlib.Topology.ContinuousMap.Defs


variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]

lemma factorisation (i : C(Y, E)) (f : C(Y, E)) [Leroy_Embedding i] :
    ∀ v : O E, (f_untenstern i).obj ((f_obenstern i).obj v)  ≤ (f_untenstern f).obj ((f_obenstern f).obj v)  →
  (∃ (g : C(Y, Y)), ∀ y : Y, f y = i (g y)) := by
  intro v h
  sorry
