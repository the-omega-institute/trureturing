/- GID: D5/S3/Quantum/Analysis/RefinedBMVLargeDegree
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVLargeDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV lower bounds for first degree at least eleven in every finite dimension. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripWideSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourKernel
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterBoundaryBridge

/-! # The refined BMV lower bounds with three copies of the second factor -/

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.LargeDegree

universe u

private theorem logKernel_mixed_neg {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu : 0 < u) (huv : u < v) :
    deriv (fun y ↦ deriv (fun x ↦ PositiveCenter.logKernel p x y) u) v < 0 := by
  by_cases hLeft : u ≤ 1 / 2
  · by_cases hShort : v - u ≤ 1
    · exact PositiveCenter.leftStrip_logKernel_mixed_lt_gap_one hp hu hLeft huv hShort
    · exact PositiveCenter.leftStrip_logKernel_mixed_lt_ge_one hp hu hLeft
        (lt_of_not_ge hShort).le
  by_cases hRight : 4 ≤ u
  · exact PositiveCenter.MiddleGapReplay.logKernel_mixed_of_lower_four_le hp hRight huv
  have huLo : 1 / 2 ≤ u := (lt_of_not_ge hLeft).le
  have huHi : u ≤ 4 := (lt_of_not_ge hRight).le
  by_cases hWide : 4 ≤ v - u
  · exact PositiveCenter.logKernel_central_gap_four_mixed_lt hp huLo huHi hWide
  by_cases hShort : v - u ≤ 1
  · exact PositiveCenter.CompactShortQuadratureCover.logKernel_mixed_lt
      hp huLo huHi huv hShort
  exact PositiveCenter.CompactTaylorModel.logKernel_mixed_neg_cleared_middle
    hp huLo huHi (lt_of_not_ge hShort).le (lt_of_not_ge hWide).le

private theorem upperPSD {p : ℕ} (hp : 11 ≤ p) : ExtremeWalk.UpperPSD.{u} p := by
  have hpPos : 0 < p := (by decide : 0 < (11 : ℕ)).trans_le hp
  exact PositiveCenter.upperPSD_of_logKernel_mixed hpPos fun _ _ hu huv ↦
    (logKernel_mixed_neg hp hu huv).le

variable {n : Type u} [Fintype n]

local instance : DecidableEq n := Classical.decEq n

/-- The product lower bound for PSD factors in any finite complex matrix space,
including singular factors. -/
theorem product_bound {p : ℕ} (hp : 11 ≤ p) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B :=
  ExtremeWalk.product_bound_all (upperPSD.{u} hp) A B hA hB

/-- The exponential lower bound for Hermitian factors in any finite complex matrix space. -/
theorem exponential_bound {p : ℕ} (hp : 11 ≤ p) (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) :=
  ExtremeWalk.exponential_bound_all (upperPSD.{u} hp) H K hH hK

#print axioms logKernel_mixed_neg
#print axioms upperPSD
#print axioms product_bound
#print axioms exponential_bound

end RefinedBMV.LargeDegree
