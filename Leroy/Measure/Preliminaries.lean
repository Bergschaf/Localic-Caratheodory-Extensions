module

public import Mathlib.Basic.Real.Basic
--import Leroy.Basic
public import Leroy.Further_Topology
public import Mathlib.Order.BoundedOrder.Basic

/-!
# Measure-theory preliminaries
-/

@[expose] public section


/-- The infimum of the set of strictly positive real numbers is zero: any lower bound
`b` of the positives must satisfy `b ≤ 0`, since otherwise the midpoint of `b` and `0`
would be a smaller positive number. -/
lemma sInf_epsilon_eq_zero : sInf {ε : Real | ε > 0} = 0 := by
  apply le_antisymm
  · rw [csInf_le_iff, lowerBounds]
    · simp only [gt_iff_lt, Set.mem_ofPred_eq]
      intro b h
      exact le_of_forall_gt_imp_ge_of_dense h
    · simp only [BddBelow, Set.Nonempty, gt_iff_lt]
      use -42
      simp only [lowerBounds, Set.mem_ofPred_eq]
      intro b h
      apply le_trans' (le_of_lt h)
      norm_num
    · simp only [Set.Nonempty, gt_iff_lt, Set.mem_ofPred_eq]
      use 42
      norm_num
  · apply le_csInf
    · simp only [Set.Nonempty, gt_iff_lt, Set.mem_ofPred_eq]
      use 42
      norm_num
    · simp only [gt_iff_lt, Set.mem_ofPred_eq]
      exact fun b a => le_of_lt a

/-- The infimum of the set of strictly positive nonnegative real numbers is zero,
the `NNReal` analogue of `sInf_epsilon_eq_zero`. -/
lemma sInf_epsilon_eq_zero' : sInf {ε : NNReal | ε > 0} = 0 := by
  apply le_antisymm
  · rw [csInf_le_iff, lowerBounds]
    · simp only [gt_iff_lt, Set.mem_ofPred_eq]
      intro b h
      exact le_of_forall_gt_imp_ge_of_dense h
    · simp only [BddBelow, Set.Nonempty, gt_iff_lt]
      use 0
      simp only [lowerBounds, Set.mem_ofPred_eq]
      intro b h
      apply le_trans' (le_of_lt h)
      norm_num
    · simp only [Set.Nonempty, gt_iff_lt, Set.mem_ofPred_eq]
      use 42
      norm_num
  · apply le_csInf
    · simp only [Set.Nonempty, gt_iff_lt, Set.mem_ofPred_eq]
      use 42
      norm_num
    · simp only [gt_iff_lt, Set.mem_ofPred_eq]
      exact fun b a => le_of_lt a
