# Perfect Observational Correlation from a Shared Source

## Abstract

Two identity observations of one fair Boolean source have conditional success probability one after observing true and zero after observing false.

**Theorem 1.1 (A fair shared source gives perfect observational correlation).**

$$\begin{aligned}\frac{\operatorname{conceptLaw}\left({u \mapsto \frac{1}{2}}, {u \mapsto (u, u)}, (true, true)\right)}{\operatorname{conceptLaw}\left({u \mapsto \frac{1}{2}}, {u \mapsto u}, true\right)} = 1,\\\frac{\operatorname{conceptLaw}\left({u \mapsto \frac{1}{2}}, {u \mapsto (u, u)}, (false, true)\right)}{\operatorname{conceptLaw}\left({u \mapsto \frac{1}{2}}, {u \mapsto u}, false\right)} = 0.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/SharedSourcePerfectCorrelation.fair_shared_source_perfect_observational_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source law assigns mass one half to each Boolean value, and both X and Y are the identity readout of that same source. The joint event X = true, Y = true therefore has mass one half, equal to the X = true marginal, so their ratio is one.

The joint event X = false, Y = true is impossible under the shared identity readout, while the X = false marginal is one half. Its conditional ratio is therefore zero.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/SharedSourcePerfectCorrelation.fair_shared_source_perfect_observational_correlation`
- Dependency: [D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence](SharedSourceObservationDependence.md)
