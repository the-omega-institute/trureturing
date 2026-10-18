/- GID: D5/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   generality: G
   mirror-B: D5/B/S3/Entropy/PoissonBinomial/MonkmanSirkerConfigurationalEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define the Poisson-binomial configurational entropy and the Monkman--Sirker majorization claim.
-/

import D5.S3.Entropy.PoissonBinomial.PoissonBinomialStructure

namespace D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy

open D5.S3.Geometry.AlphaGeometry.PositiveSimplexGeometryAndMixing (moreMixed)

def claim : Prop :=
  ∀ (M : ℕ) (c d : Fin M → ℝ),
    (∀ i, c i ∈ Set.Icc 0 1) →
    (∀ i, d i ∈ Set.Icc 0 1) →
    moreMixed d c → F c ≤ F d

end D5.S3.Entropy.PoissonBinomial.MonkmanSirkerConfigurationalEntropy
