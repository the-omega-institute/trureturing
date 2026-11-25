/- GID: D5/S0/Conventions/GeometricWeights
   generality: I
   mirror-B: D5/B/S0/Conventions/GeometricWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: No nonzero rational rescaling of geometric weights matches all singleton W weights. -/

module
prelude
public import D5.S0.Conventions.CanonicalDigits.Geometric

namespace D5.S0.Conventions.GeometricWeights

open Omega Omega.Arithmetic.WDigits

/-- Geometric weights cannot reproduce all singleton Zeckendorf weights up to nonzero scale. -/
public theorem no_geometric_weights_match_zeckendorf_singletons :
    Not (Exists fun first : FiniteRatio => Exists fun ratio : FiniteRatio =>
      Exists fun scale : FiniteRatio =>
        And (Not (Eq scale.num Int.zero)) (MatchesScaledWeights first ratio scale)) :=
  no_scaled_geometric_weights

end D5.S0.Conventions.GeometricWeights
