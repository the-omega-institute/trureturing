# ConfigurationCharge

## Abstract

The occupation defect is the expectation of the exact signed configuration charge under one actual common-activity Gibbs law.

The carrier is an arbitrary finite type, including the empty type. The graph is simple and the common real activity lambda is strictly positive. Configurations are all actual independent subsets, including the empty set. The existing GibbsOccupation law gives mass lambda to the power of the configuration cardinality divided by the actual partition sum. Every vertex weight and every expectation below use this same graph and activity. In the formulas, O(G,J,v), q(G,lambda,v), C(G,lambda,J) and D(G,lambda) denote occupiedNeighbors, degreeWeight, configurationCharge and occupationDefect. Z(G,lambda) is the sum of lambda to the cardinality of J over configurations(G,univ); M(G,lambda) is meanOccupation(G,univ,lambda), identified with the actual PMF expectation by GibbsOccupation.gibbs_expected_card.

**Definition 1.1 (Occupied neighbors).**

$$\operatorname{O}\left(G, J, v\right) = \{u \in J\mid\operatorname{Adj}\left(G, v, u\right)\}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupiedNeighbors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The occupied neighbors of v are precisely the members of J adjacent to v, so their cardinality is the source random variable Y_v.

**Definition 1.2 (Common-activity degree weight).**

$$\operatorname{q}\left(G, \lambda, v\right) = \frac{\lambda}{1 + \left(\operatorname{degree}\left(G, v\right) + 1\right) \cdot \lambda}$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.degreeWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight q_v is lambda divided by 1 plus (degree(v) plus 1) times lambda; for positive lambda it is also the reciprocal of degree(v) plus 1 plus 1/lambda.

**Definition 1.3 (Exact signed configuration charge).**

$$\operatorname{C}\left(G, \lambda, J\right) = \sum_{v \in V,2 \le \operatorname{card}\left(\operatorname{O}\left(G, J, v\right)\right)} (\sum_{u \in \operatorname{O}\left(G, J, v\right)} (\operatorname{q}\left(G, \lambda, u\right)) - \operatorname{q}\left(G, \lambda, v\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.configurationCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum over all v with at least two occupied neighbors of the sum of q_u over those occupied neighbors minus q_v. The charge is signed; neither it nor its expectation is asserted nonnegative.

**Definition 1.4 (Actual occupation defect).**

$$\operatorname{D}\left(G, \lambda\right) = \operatorname{M}\left(G, \lambda\right) - \sum_{v \in V} (\operatorname{q}\left(G, \lambda, v\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupationDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean actual Gibbs configuration cardinality minus the sum of the degree weights.

**Theorem 1.5 (Actual Gibbs defect equals expected source charge).**

$$\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall lambda \in \mathbb{R},\; 0 < lambda \Rightarrow \operatorname{D}\left(G, lambda\right) = \sum_{J \in \operatorname{configurations}\left(G, \operatorname{univ}\left(V\right)\right)} (\frac{lambda^{\operatorname{card}\left(J\right)}}{\operatorname{Z}\left(G, lambda\right)} \cdot \operatorname{C}\left(G, lambda, J\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.defect_eq_expected_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the complete source identity: D equals the sum over actual independent configurations J of P(J) times C(J). The finite sum is also written using the existing actual Gibbs PMF. There is no local-balance certificate, assumed normalization, arbitrary marginal law, finite periodic proxy or nonempty-graph premise.

The proof exchanges the sole occupied neighbor u of v with v. Independence supplies the reverse singleton-neighbor condition; the inverse exchange and equal cardinality preserve the common-activity weight. Opposite directed singleton contributions therefore cancel in expectation. The zero-neighbor contribution follows from the existing actual deletion partition identity and marked-weight identity. Finite double counting and the degree-weight denominator then give the exact defect. Empty carriers and edgeless graphs are included by the same finite sums.

The configuration law, deletion partitions, occupation moments and finite PMF expectation all refer to the same independent-set family. The exchange acts on one configuration at a time and preserves its common-activity weight.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.configurationCharge`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.defect_eq_expected_charge`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.degreeWeight`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupationDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupiedNeighbors`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/GibbsOccupation](GibbsOccupation.md)
