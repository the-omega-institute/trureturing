/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq207NormalizationDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq207NormalizationDefs
   mirror-E: none(waiver:formal-right-root-series)
   anchors: []
   utility: none
   digest: Finite coefficient sums construct the normalized tree and its scalar resolvent. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207Catalytic
import D5.S3.Combinatorics.InversionSeq.InversionSeq207Tridiagonal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq207Normalization

open InversionSeq207Endpoints InversionSeq207Tridiagonal

noncomputable def rightNormalized : PowerSeries (Polynomial ℚ) :=
  let alternating : PowerSeries (Polynomial ℚ) := PowerSeries.mk fun degree => (-1) ^ degree
  let geometric : PowerSeries (Polynomial ℚ) :=
    PowerSeries.mk fun degree => Polynomial.X ^ degree
  PowerSeries.mk fun degree =>
    ∑ depth ∈ Finset.range (degree + 1),
      (walkEndpoints false depth).sum fun label weight =>
        (weight : ℚ) • PowerSeries.coeff degree
          (PowerSeries.X ^ depth * alternating ^ (2 * depth) *
            (1 + PowerSeries.X) ^ label.1 *
            PowerSeries.C ((1 - Polynomial.X) ^ label.1) * geometric ^ (label.1 + 1))

noncomputable def rightScalarSeries : PowerSeries ℚ :=
  (1 - PowerSeries.X) * PowerSeries.mk fun degree =>
    ∑ index ∈ Finset.range (degree + 1), PowerSeries.coeff degree (tridiagonalSeries index)

end D5.S3.Combinatorics.InversionSeq.InversionSeq207Normalization
