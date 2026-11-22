/- GID: D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVThreeSpectrumCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The all-degree refined BMV lower bounds with at most three spectral values. -/

import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedBinding
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedRows0
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedRows1
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedRows2
import D5.S3.Quantum.Analysis.RefinedBMV.ThreeSpectrum.GroupedRows3
import D5.S3.Quantum.Analysis.RefinedBMVThreeSpectrumReduction

/-! The refined BMV lower bounds in every positive degree with at most three
spectral values of the first matrix. -/

namespace RefinedBMV.DividedDifference

open SparseExpansion SparseExpansion.GroupedMasks

private theorem checked_masks : GroupedMasks.quartic.checkMasks = true := by
  have hx : GroupedMasks.quartic.rootsX.length = 65 := by decide +kernel
  have hparts :
      List.range 65 = List.range' 0 16 ++ List.range' 16 16 ++
        List.range' 32 16 ++ List.range' 48 17 := by decide +kernel
  unfold Certificate.checkMasks
  rw [rates_checked, hx, hparts]
  simp only [List.all_append, rows_0, rows_1, rows_2, rows_3, Bool.true_and]

set_option maxRecDepth 4096 in
private theorem logGap_nonneg (p s t : ℝ) (hp : 1 ≤ p) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ clearedQuartic p (Real.exp (3 * s)) (Real.exp (3 * (s + t)))
      (Real.exp (p * s)) (Real.exp (p * (s + t))) := by
  exact nonneg_of_static_check GroupedMasks.quartic.terms GroupedMasks.quartic.rootsX GroupedMasks.quartic.rootsY
    quartic_matches_grouped certificateStatic (GroupedMasks.quartic.masks_of_check checked_masks) p s t hp hs ht

/-- The checked quartic on nonnegative roots in increasing order. -/
theorem ordered_quartic_nonneg (p : ℕ) (hp : 0 < p) {a x y : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) : 0 ≤ quartic p a x y := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact quartic_nonneg_of_log_gaps p (fun s t hs ht => logGap_nonneg p s t hp' hs ht)
    ha hax hxy

open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- The all-degree product lower bound for at most three spectral values. -/
theorem three_spectrum_product {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact product_bound_of_log_gaps p A B hA hB hs (fun s t h₁ h₂ =>
    logGap_nonneg p s t hp' h₁ h₂)

/-- The all-degree exponential lower bound for at most three spectral values. -/
theorem three_spectrum_exponential {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hs : (Finset.univ.image hH.eigenvalues).card ≤ 3) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact exponential_bound_of_log_gaps p H K hH hK hs (fun s t h₁ h₂ =>
    logGap_nonneg p s t hp' h₁ h₂)

#print axioms three_spectrum_product
#print axioms three_spectrum_exponential

end RefinedBMV.DividedDifference
