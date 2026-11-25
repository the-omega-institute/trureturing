/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FiniteProduct
   generality: G
   mirror-B: none(waiver:proof-pending-delivery)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Four-copy refined BMV lower bounds through degree ten for spectra of cardinality at most three. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FiniteDegreeSigns
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.SpectrumEndpoint

/-! The reciprocal-gap certificates supply all six Gram signs in each
degree from one to ten, with arbitrary spectral multiplicities. -/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

theorem product_bound_lt_eleven {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) (hsmall : p < 11)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hcard : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B :=
  product_bound_of_three_value_signs p hp A B hA hB hcard
    (fun r t hr hr₁ ht ht₁ => sixSigns_of_degree_lt_eleven p hp hsmall hr hr₁.le ht ht₁.le)

#print axioms product_bound_lt_eleven

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
