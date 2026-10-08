/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207Polynomials
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207Polynomials
   mirror-E: none(waiver:formal-laurent-polynomial-system)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Euler convolution defines the generating series for the symmetric polynomial system. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler
import Mathlib.RingTheory.PowerSeries.Expand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials

open InversionSeq207Euler

noncomputable def polynomialGenerator : PowerSeries (LaurentPolynomial (PowerSeries ℚ)) :=
  let lift := LaurentPolynomial.C.comp (PowerSeries.expand 2 (by decide)).toRingHom
  let euler := PowerSeries.map lift (PowerSeries.mk eulerCoefficients)
  let numerator := PowerSeries.rescale (LaurentPolynomial.C PowerSeries.X) euler
  let denominator := PowerSeries.rescale (LaurentPolynomial.T 1) euler *
    PowerSeries.rescale (LaurentPolynomial.T (-1)) euler
  numerator ^ 2 * PowerSeries.invOfUnit denominator 1

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Polynomials
