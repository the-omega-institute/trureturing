/- GID: D5/S3/Quantum/Analysis/RefinedBMVLargeDegree
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVLargeDegree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The refined BMV lower bounds with three copies of the second factor in every finite dimension. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureCover
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripGeometricSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.LeftStripWideSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleGapReplay
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.SeparatedFourKernel
import D5.S3.Quantum.Analysis.RefinedBMV43
import D5.S3.Quantum.Analysis.RefinedBMVExtremeAnalytic
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
private theorem product_bound {p : ℕ} (hp : 11 ≤ p) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B :=
  ExtremeWalk.product_bound_all (upperPSD.{u} hp) A B hA hB

/-- The exponential lower bound for Hermitian factors in any finite complex matrix space. -/
private theorem exponential_bound {p : ℕ} (hp : 11 ≤ p) (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) :=
  ExtremeWalk.exponential_bound_all (upperPSD.{u} hp) H K hH hK

private theorem wordMean_three (A B : Matrix n n ℂ) :
    DimThree.wordMean 3 A B = RefinedBMV.wordMean A B := by
  rw [RefinedBMV.wordMean_eq_enumerated]
  have hlength : (balancedWords 3 3).length = 20 := by simp [balancedWords]
  simp only [DimThree.wordMean, hlength, Nat.cast_ofNat]

private theorem wordMean_four (A B : Matrix n n ℂ) :
    DimThree.wordMean 4 A B = mean43 A B := by
  rw [mean43_eq_enumerated]
  simp only [DimThree.wordMean, balancedWords43_count.1, Nat.cast_ofNat]

/-- The refined product lower bound for every first count at least three
and every finite complex matrix space. -/
theorem product_bound_all {p : ℕ} (hp : 3 ≤ p) (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  by_cases hlarge : 11 ≤ p
  · exact product_bound hlarge A B hA hB
  have hsmall : p ≤ 10 := by omega
  interval_cases p
  · rw [wordMean_three, show ((3 : ℕ) : ℝ) / 3 = 1 by norm_num, CFC.rpow_one A hA.nonneg]
    exact E33_all A B hA hB
  · simpa only [Nat.cast_ofNat, wordMean_four] using E43_all A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_five A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_six A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_seven A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_eight A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_nine A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_ten A B hA hB

/-- The refined exponential lower bound for every first count at least three
and every finite complex matrix space. -/
theorem exponential_bound_all {p : ℕ} (hp : 3 ≤ p) (H K : Matrix n n ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  by_cases hlarge : 11 ≤ p
  · exact exponential_bound hlarge H K hH hK
  have hsmall : p ≤ 10 := by omega
  interval_cases p
  · rw [wordMean_three]
    exact (ThreeSpectralValues.trace_exp_le_cube H K hH hK).trans
      (E33_all _ _ hH.isSelfAdjoint.exp_nonneg.posSemidef hK.isSelfAdjoint.exp_nonneg.posSemidef)
  · simpa only [Nat.cast_ofNat, wordMean_four] using L43_all H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_five H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_six H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_seven H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_eight H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_nine H K hH hK
  · simpa only [Nat.cast_ofNat] using Extreme.exponential_bound_ten H K hH hK

#print axioms logKernel_mixed_neg
#print axioms upperPSD
#print axioms product_bound
#print axioms exponential_bound
#print axioms product_bound_all
#print axioms exponential_bound_all

end RefinedBMV.LargeDegree
