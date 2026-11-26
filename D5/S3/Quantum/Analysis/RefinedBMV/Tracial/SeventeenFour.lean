/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SeventeenFour
   generality: G
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The degree-seventeen four-copy trace comparison for three spectral values. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.SeventeenFourThreeSpectrum
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusPositive

/-! The ordered-word mean dominates the balanced product for a positive
semidefinite first factor with three spectral values. -/

namespace RefinedBMV.Tracial

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-- A positive semidefinite first factor with spectrum contained in three
ordered nonnegative values satisfies the `(17,4)` refined BMV comparison
against every Hermitian second factor, in any finite dimension. -/
theorem seventeen_four_of_three_spectral_values {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.IsHermitian)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbc : b < c)
    (hspectrum : ∀ i, ∃ j : Fin 3,
      hA.isHermitian.eigenvalues i = (![a, b, c] : Fin 3 → ℝ) j) :
    trace (((A ^ ((17 : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean 17 A B := by
  classical
  apply TriangleSurplus.product_bound_of_positive_surplus _ A B hA hB ha hab hbc
    (fun i ↦ Classical.choose (hspectrum i)) (fun i ↦ Classical.choose_spec (hspectrum i))
  intro x y hx hy
  obtain ⟨h₀₁, h₀₂, h₁₂⟩ := TriangleSurplus.surplus_pos x y hx hy
  exact ⟨h₀₁, h₀₂.le, h₁₂.le⟩

#print axioms seventeen_four_of_three_spectral_values

end

end RefinedBMV.Tracial
