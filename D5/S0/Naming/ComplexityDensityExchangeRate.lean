/- GID: D5/S0/Naming/ComplexityDensityExchangeRate
   generality: G
   mirror-B: D5/B/S0/Naming/ComplexityDensityExchangeRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive limiting complexity densities have quotient equal to the entropy exchange rate. -/

import Mathlib.Topology.Instances.Real.Lemmas

namespace D5.S0.Naming.ComplexityDensityExchangeRate

open Filter

/-- Once the two Brudno complexity-density limits are available for positive-entropy
towers, their pointwise quotient converges to the quotient of the tower entropies.
Positivity records the source theorem's positive-entropy regime and, for the denominator,
excludes Lean's totalized division-by-zero branch. -/
theorem complexity_density_ratio_tendsto_entropy_ratio
    {Index : Type*} {l : Filter Index}
    (density1 density2 : Index -> Real)
    (h1 h2 : Real)
    (_h1Positive : 0 < h1)
    (h2Positive : 0 < h2)
    (density1Limit : Tendsto density1 l (nhds h1))
    (density2Limit : Tendsto density2 l (nhds h2)) :
    Tendsto (fun index => density1 index / density2 index) l (nhds (h1 / h2)) := by
  exact density1Limit.div density2Limit (ne_of_gt h2Positive)

end D5.S0.Naming.ComplexityDensityExchangeRate
