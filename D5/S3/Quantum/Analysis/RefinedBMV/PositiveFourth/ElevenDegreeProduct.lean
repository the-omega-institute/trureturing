/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/ElevenDegreeProduct
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The eleven-four trace product lower bound for three spectral values. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FiniteGapCircuit
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.SpectrumEndpoint

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedEleven (sign : GramSign) : checkFiniteSign 11 sign = true := by
  cases sign <;> decide +kernel

/-- The four-copy product comparison at degree eleven for arbitrary finite
dimension and at most three spectral values of the first factor. -/
theorem product_bound_eleven {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hcard : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3) :
    trace (((A ^ ((11 : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean 11 A B :=
  product_bound_of_three_value_signs 11 (by decide) A B hA hB hcard
    (fun r t hr hr₁ ht ht₁ => finiteSigns_of_checks 11 checkedEleven hr hr₁.le ht ht₁.le)

#print axioms product_bound_eleven

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
