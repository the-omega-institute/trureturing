/- GID: D5/S3/Arith/FibonacciAtomic/FixedLengthRealResponseRank
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FixedLengthRealResponseRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The real response matrix on all raw assignments has rank two to the crossing count. -/
import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxRecDepth 4096
namespace D5.S3.Arith.FibonacciAtomic.FixedLengthRealResponseRank
open FirstRejectionCutCapacity
open LiteralWindowEnd (Window first last)
open scoped BigOperators

/-- The real matrix is indexed by all assignments on both coordinate sides. -/
noncomputable def responseMatrix {k : ℕ} (A : Finset (Fin (k + 1))) :
    Matrix (Side k A) ({r : Fin (k + 1) // r ∉ A} → Window) ℝ :=
  fun a b => if boolean (merge A a b) then 1 else 0

-- Temporary API probe; removed before the final mathematical delivery.
#check Matrix.rank_mul_le_left
#check Matrix.rank_mul_le_right
#check Matrix.rank_submatrix_le
#check Matrix.rank_le_card_width
#check Matrix.rank_le_card_height
#check Matrix.rank_of_isUnit
#check Matrix.rank_eq_finrank_span_row
#check LinearIndependent.rank_matrix
#check Matrix.kroneckerMap
#check Matrix.det_kronecker
#check Matrix.mul_eq_one_comm
#check Fintype.prod_sum
#check Finset.prod_univ_sum
#check Fintype.piFinset
#check Finset.inf_eq_top
#check Finset.prod_eq_zero_iff
#check Matrix.one_apply

end D5.S3.Arith.FibonacciAtomic.FixedLengthRealResponseRank
