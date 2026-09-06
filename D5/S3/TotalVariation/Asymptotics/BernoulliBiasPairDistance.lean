/- GID: D5/S3/TotalVariation/Asymptotics/BernoulliBiasPairDistance
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Asymptotics/BernoulliBiasPairDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact total variation between any two canonical Bool bias laws is the absolute bias difference. -/

import D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData

/-!
# Exact distance between two canonical Bernoulli bias laws

The repository already owns `positiveBiasLaw delta`, whose true mass is
`1/2+delta`, and the finite total-variation normalization.  Searches found the
special symmetric `+delta` versus `-delta` closed form, but no public theorem
for two arbitrary bias parameters.  This module adds only that missing generic
identity.

The equality is algebraic for all real parameters.  Probability semantics can
be supplied separately by the existing closed-range theorem
`bias_laws_probability_data`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.TotalVariation.Asymptotics.BernoulliBiasPairDistance

open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Pinsker

/-- Exact total variation between two canonical positive-bias Bool laws. -/
theorem positive_bias_pair_total_variation (delta epsilon : ℝ) :
    totalVariation (positiveBiasLaw delta) (positiveBiasLaw epsilon) =
      |delta - epsilon| := by
  rw [totalVariation, Fintype.sum_bool]
  simp only [positiveBiasLaw, Bool.false_eq_true, ↓reduceIte]
  have htrue :
      1 / 2 + delta - (1 / 2 + epsilon) = delta - epsilon := by ring
  have hfalse :
      1 / 2 - delta - (1 / 2 - epsilon) = -(delta - epsilon) := by ring
  rw [htrue, hfalse, abs_neg]
  ring

/-- In plus-port probability coordinates, total variation is exactly the
absolute probability gap. -/
theorem plus_probability_pair_total_variation (p q : ℝ) :
    totalVariation
        (positiveBiasLaw (p - 1 / 2))
        (positiveBiasLaw (q - 1 / 2)) = |p - q| := by
  rw [positive_bias_pair_total_variation]
  congr 1
  ring

#print axioms positive_bias_pair_total_variation
#print axioms plus_probability_pair_total_variation

end D5.S3.TotalVariation.Asymptotics.BernoulliBiasPairDistance
