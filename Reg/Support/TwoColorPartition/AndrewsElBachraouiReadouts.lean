import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs
import D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiBounds

/-! Concrete observations used solely by the source-bound registration proofs. -/

namespace Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
open PowerSeries Finset
open _root_.D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs

theorem dCoeff_zero : dCoeff 2 1 0 = 0 := by
  simp [dCoeff, dTrunc, geom, coeff_mk]

theorem dCoeff_two : dCoeff 2 1 2 = 1 := by
  norm_num [dCoeff, dTrunc, sum_range_succ, prod_range_succ, coeff_X_pow_mul', geom, coeff_mk]

end Reg.Support.TwoColorPartition.AndrewsElBachraouiReadouts
