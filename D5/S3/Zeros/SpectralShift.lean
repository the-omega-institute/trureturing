/- GID: D5/S3/Zeros/SpectralShift
   generality: I
   mirror-B: D5/B/S3/Zeros/SpectralShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize multiplicative address shifts as eigen-actions on the labeled zeta vector. -/

import D5.S1.Digit.PrimeAxisAddition
import D5.S3.Weil.SpectralHilbert

namespace D5.S3.Zeros.SpectralShift

open D5.S1.Digit
open D5.S3.Weil.Convention
open D5.S3.Weil.SpectralHilbert

/-- Pull a coefficient family backward along multiplication by the address `u`. -/
noncomputable def backwardShift (u : PrimeAxisTable)
    (x : PrimeAxisTable → ℂ) : PrimeAxisTable → ℂ :=
  fun a ↦ x (normalizedTableAdd a u)

/-- The raw labeled-zeta family is an eigenfamily for every multiplicative address shift. -/
theorem labeled_zeta_backward_shift_eigen (s : ℂ) (u a : PrimeAxisTable) :
    backwardShift u (labeledZetaCoefficient s) a =
      labeledZetaCoefficient s u * labeledZetaCoefficient s a := by
  simp [backwardShift, labeledZetaCoefficient, normalizedTableAdd,
    Complex.natCast_mul_natCast_cpow, one_div]

/-- In its square-summable domain, the labeled-zeta Hilbert vector has the same eigenvalue. -/
theorem labeled_zeta_vector_backward_shift_eigen (s : ℂ)
    (hs : criticalAbscissa < s.re) (u a : PrimeAxisTable) :
    backwardShift u (labeledZetaVector s hs) a =
      labeledZetaCoefficient s u * labeledZetaVector s hs a := by
  simpa [backwardShift] using labeled_zeta_backward_shift_eigen s u a

end D5.S3.Zeros.SpectralShift
