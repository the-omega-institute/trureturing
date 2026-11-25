/- GID: D5/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/ZeroCenter/Endpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The singular four-spectrum refined BMV bound at every positive degree. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeAnalytic
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Compact
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Middle
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.NearCover
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.SmallDegrees
import D5.S3.Quantum.Analysis.RefinedBMV.ZeroCenter.Tail

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace RefinedBMV.FourSpectrumLift

universe u

/-- Refined BMV trace lower bound at every positive degree for a singular positive
semidefinite spectrum with at most four distinct eigenvalues. -/
theorem product_bound_singular_all {n : Type u} [Fintype n] [DecidableEq n]
    {p : ℕ} (hp : 0 < p)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hSing : A.det = 0) (hs : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 4) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  -- The degree-five through degree-ten endpoints use `Classical.decEq`.
  cases Subsingleton.elim (inferInstance : DecidableEq n) (Classical.decEq n)
  letI : DecidableEq n := Classical.decEq n
  by_cases hp₁₁ : 11 ≤ p
  · refine product_bound_singular hp (zeroUpperPSD_of_profile_curvature hp ?_) A B hA hB hSing hs
    intro c hc
    by_cases hc₁ : c ≤ 1
    · exact (zeroProfile_deriv2_pos_small hp₁₁ hc hc₁).le
    by_cases hc₄ : c < 4
    · exact (zeroProfile_deriv2_pos_middle hp₁₁ (le_of_not_ge hc₁) hc₄.le).le
    by_cases hc₃₂ : c ≤ 32
    · exact (zeroProfile_deriv2_pos_of_four_le hp₁₁ (le_of_not_gt hc₄) hc₃₂).le
    exact (zeroProfile_tail_curvature_pos hp (le_of_lt (lt_of_not_ge hc₃₂))).le
  rcases (show p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 ∨
    p = 9 ∨ p = 10 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact product_bound_singular (p := 1) (by decide)
      (zeroUpperPSD_of_profile_curvature (by decide) (fun _ hc ↦ (zeroProfile_curvature_one hc).le))
      A B hA hB hSing hs
  · exact product_bound_singular (p := 2) (by decide)
      (zeroUpperPSD_of_profile_curvature (by decide) (fun _ hc ↦ (zeroProfile_curvature_two hc).le))
      A B hA hB hSing hs
  · have hCount : (balancedWords 3 3).length = 20 := by simp [balancedWords]
    rw [show ((3 : ℕ) : ℝ) / 3 = 1 by norm_num, CFC.rpow_one A hA.nonneg]
    simpa only [DimThree.wordMean, hCount, Nat.cast_ofNat, wordMean_eq_enumerated] using
      E33_all A B hA hB
  · have hCount := balancedWords43_count.1
    simpa only [DimThree.wordMean, hCount, Nat.cast_ofNat, mean43_eq_enumerated] using
      E43_all A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_five A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_six A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_seven A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_eight A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_nine A B hA hB
  · simpa only [Nat.cast_ofNat] using Extreme.product_bound_ten A B hA hB

#print axioms product_bound_singular_all

end RefinedBMV.FourSpectrumLift
