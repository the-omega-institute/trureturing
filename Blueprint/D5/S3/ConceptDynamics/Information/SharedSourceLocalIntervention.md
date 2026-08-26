# Shared-Source Local Intervention

## Abstract

Fixing one coordinate leaves a distinct shared-source coordinate fair and unfixed.

**Theorem 1.1 (A local intervention exposes the retained shared source).**

$$\forall Address \in Type, p \in Address, q \in Address,\; \left(\operatorname{DecidableEq}\left(Address\right) \land p \ne q\right) \Rightarrow \left(\forall imposed \in Bool, source \in Bool, observed \in Bool,\; \operatorname{ite}\left(q = p, imposed, source\right) = source \land \left(\operatorname{conceptLaw}\left(\Lambda fairSource, \frac{1}{2}, \Lambda source, \operatorname{ite}\left(q = p, imposed, source\right), observed\right) = \frac{1}{2} \land \operatorname{conceptLaw}\left(\Lambda fairSource, \frac{1}{2}, \Lambda source, \operatorname{decide}\left(\operatorname{ite}\left(q = p, imposed, source\right) \ne imposed\right), true\right) = \frac{1}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/SharedSourceLocalIntervention.local_intervention_exposes_shared_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p and q be distinct decidable addresses. The local intervention replaces the value at p by an imposed Boolean value, while the value queried at q remains the Boolean source.

With mass one half on each source state, the q-coordinate therefore retains mass one half at each Boolean value. It also differs from the imposed p-coordinate with probability one half.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/SharedSourceLocalIntervention.local_intervention_exposes_shared_source`
- Dependency: [D5/S3/ConceptDynamics/Information/SharedSourceObservationDependence](SharedSourceObservationDependence.md)
