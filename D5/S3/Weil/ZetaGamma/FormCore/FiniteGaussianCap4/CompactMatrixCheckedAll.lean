/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixCheckedAll
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianCap475.finiteGaussian_actual_head_certificate; premises=D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixCheckedAll.compactMomentMatrix_bounds
   digest: Every actual signed compact matrix entry lies within its original center error bound. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowZeroLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowZeroUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowOneLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowOneUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowTwoLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowTwoUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowThreeLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowThreeUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFourLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFourUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFiveLower
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFiveUpper
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowSix
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowSeven
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowEight
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowNine
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowTen
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowEleven
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowTwelve
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowThirteen
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFourteen
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCheckedRowFifteen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

noncomputable section
namespace FiniteGaussianCap475
open Polynomial
open FiniteGaussianCap4.LaguerreSevenHalf.RationalModel
open D5.S0.Certificates.BoxCover.RationalIntervalExpression

private theorem centerQ_symm :
    ∀ i j : Fin 16, Cap4FiniteCertificate.centerQ i j =
      Cap4FiniteCertificate.centerQ j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem center_symm (i j : Fin 16) :
    Cap4FiniteCertificate.center i j = Cap4FiniteCertificate.center j i := by
  change (Cap4FiniteCertificate.centerQ i j : ℝ) =
    (Cap4FiniteCertificate.centerQ j i : ℝ)
  rw [centerQ_symm i j]

private theorem upper_triangle_bound (i j : Fin 16) (hij : i ≤ j) :
    |compactMomentMatrix i j - Cap4FiniteCertificate.center i j| <
      (1 / 1000000000 : ℝ) := by
  fin_cases i
  · by_cases hj : j.val < 8
    · exact row_zero_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_zero_upper_bounds j (le_of_not_gt hj) j.isLt
  · by_cases hj : j.val < 8
    · exact row_one_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_one_upper_bounds j (le_of_not_gt hj) j.isLt
  · by_cases hj : j.val < 9
    · exact row_two_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_two_upper_bounds j (le_of_not_gt hj) j.isLt
  · by_cases hj : j.val < 9
    · exact row_three_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_three_upper_bounds j (le_of_not_gt hj) j.isLt
  · by_cases hj : j.val < 10
    · exact row_four_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_four_upper_bounds j (le_of_not_gt hj) j.isLt
  · by_cases hj : j.val < 10
    · exact row_five_lower_bounds j (by simpa [Fin.le_def] using hij) hj
    · exact row_five_upper_bounds j (le_of_not_gt hj) j.isLt
  · exact row_six_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_seven_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_eight_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_nine_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_ten_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_eleven_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_twelve_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_thirteen_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_fourteen_bounds j (by simpa [Fin.le_def] using hij) j.isLt
  · exact row_fifteen_bounds j (by simpa [Fin.le_def] using hij) j.isLt

/-- Every actual signed compact matrix entry, including both triangles,
obeys the original entrywise error bound without any input hypothesis. -/
theorem compactMomentMatrix_bounds (i j : Fin 16) :
    |compactMomentMatrix i j - Cap4FiniteCertificate.center i j| <
      (1 / 1000000000 : ℝ) := by
  by_cases hij : i ≤ j
  · exact upper_triangle_bound i j hij
  · rw [compactMomentMatrix_symm i j, center_symm i j]
    exact upper_triangle_bound j i (le_of_lt (lt_of_not_ge hij))

end FiniteGaussianCap475
