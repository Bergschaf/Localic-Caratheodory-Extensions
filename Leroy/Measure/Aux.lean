import Mathlib.Data.Real.Basic
--import Leroy.Basic
import Leroy.Further_Topology
import Mathlib.Order.BoundedOrder.Basic



lemma sInf_epsilon_eq_zero : sInf {ε : Real | ε > 0} = 0 := by
      apply le_antisymm
      . rw [csInf_le_iff, lowerBounds]
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        intro b h
        exact le_of_forall_gt_imp_ge_of_dense h
        simp only [BddBelow, Set.Nonempty, gt_iff_lt]
        use -42
        simp only [lowerBounds, Set.mem_setOf_eq]
        intro b h
        apply le_trans' (le_of_lt h)
        norm_num
        simp [Set.Nonempty]
        use 42
        norm_num

      . apply le_csInf
        simp only [Set.Nonempty, gt_iff_lt, Set.mem_setOf_eq]
        use 42
        norm_num
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        exact fun b a => le_of_lt a

lemma sInf_epsilon_eq_zero' : sInf {ε : NNReal | ε > 0} = 0 := by
      apply le_antisymm
      . rw [csInf_le_iff, lowerBounds]
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        intro b h
        exact le_of_forall_gt_imp_ge_of_dense h
        simp only [BddBelow, Set.Nonempty, gt_iff_lt]
        use 0
        simp only [lowerBounds, Set.mem_setOf_eq]
        intro b h
        apply le_trans' (le_of_lt h)
        norm_num
        simp [Set.Nonempty]
        use 42
        norm_num

      . apply le_csInf
        simp only [Set.Nonempty, gt_iff_lt, Set.mem_setOf_eq]
        use 42
        norm_num
        simp only [gt_iff_lt, Set.mem_setOf_eq]
        exact fun b a => le_of_lt a
