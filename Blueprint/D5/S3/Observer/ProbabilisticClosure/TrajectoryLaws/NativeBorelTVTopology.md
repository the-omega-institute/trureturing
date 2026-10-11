# Borel law transport

## Abstract

Total variation and complete coordinates

## Complete legal laws and residual measurability

ProbabilityMeasure(ValidTail(s)) is the existing probability-law carrier, and Regular is exactly the source emission interval and all source tail bounds. Infinity remains in ValidTail and in every coordinate comparison. Simplex(s) consists of all ENNReal coordinate functions with countable sum one. No finite-support condition is imposed.

**Definition 1.1 (coordinateEquiv).**

$$\forall s: ActivePhase, \operatorname{MeasurableEquiv}\left(\operatorname{coordinateEquiv}\left(s\right), \operatorname{ProbabilityMeasure}\left(\operatorname{ValidTail}\left(s\right)\right), \operatorname{Simplex}\left(s\right)\right)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map takes every singleton mass. The inverse is the countable sum of mass(t) times Dirac(t). Singleton reconstruction proves both inverse identities, and measurable evaluation and countable sums prove measurability in both directions. This identifies Giry with complete-coordinate measurability. The complete-coordinate topology theorem uses this equivalence and the finite TV estimate to identify the original TV topology and Borel sets for all laws.

**Theorem 1.2 (regular measurable).**

$$\forall s: ActivePhase, \operatorname{MeasurableSet}\left(\operatorname{RegularSet}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.regular_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RegularSet(s) is the set of probability laws D satisfying Regular(s,D), with the unchanged interval [1/3,2/5], tail rate 4/15, and suspended tail factor 2/5. Each inequality is measurable and the intersection is countable. The explicit simplex equivalence transports standard-Borel structure to probability laws; this measurable regularity set then gives the original RegularDescriptor subtype standard-Borel structure.

**Theorem 1.3 (regular infinity zero).**

$$\forall s: ActivePhase, \forall D: RegularDescriptor, \operatorname{mass}\left(\operatorname{law}\left(D\right), \operatorname{infinity}\left(s\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.regular_infinity_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D ranges over RegularDescriptor(s). Every tailSet(s,j) contains infinity. Its mass bounds that singleton and tends to zero, including the suspended factor. Infinity is retained as a coordinate; its zero mass is derived from regularity.

**Theorem 1.4 (residualB measurable).**

$$\operatorname{Measurable}\left(\operatorname{residualB}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.residualB_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

residualB maps PDescriptor into the entire measure space on ValidTail(beta). The range of prependB is the complement of the first alpha atom. Its comap mass is exactly 1-u, so the normalized residual is a probability measure. The reciprocal is finite because 3/5 <= 1-u <= 2/3. No opposite regularity premise is used.

**Theorem 1.5 (residualA measurable).**

$$\operatorname{Measurable}\left(\operatorname{residualA}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.residualA_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

residualA maps BDescriptor into the entire measure space on ValidTail(p). The range of prependA is the complement of betaStop. Its comap mass is v and 1/3 <= v <= 2/5, so normalization gives a probability measure. Comap evaluation and the same original input emission give measurability.

**Theorem 1.6 (tv finite coordinate bound).**

$$\forall s: ActivePhase, \forall P: ProbabilityMeasureValidTail, \forall Q: ProbabilityMeasureValidTail, \forall F: FinsetValidTail, \operatorname{TV}\left(P, Q\right)\leq\operatorname{ofReal}\left(\operatorname{finiteCoordinateGapPlusTail}\left(P, Q, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_finite_coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P and Q range over all probability laws on ValidTail(s), and F is any finite set of complete atoms. finiteCoordinateGapPlusTail means sum over t in F of abs[P.real{t}-Q.real{t}] plus P.real(complement F). TV is exactly the repository event-supremum of the maximum of the two ENNReal directed differences. Split an event over F and its complement; the reverse difference follows by applying the same bound to the complementary event and using both total masses equal to one. This establishes the finite-coordinate TV neighborhood estimate without assuming a weak-topology identification. Finite approximation and both neighborhood directions establish the corresponding topology and Borel equality in NativeBorelTVTopology.

For each active phase, the carrier is the entire probability-law space on ValidTail(s). The distance is the supremum over all measurable events of the maximum of the two directed ENNReal gaps. tvTopology is the topology generated by this distance, and coordinateTopology is induced by the complete singleton-coordinate equivalence into Simplex(s). Infinity belongs to the carrier and the coordinate map.

**Theorem 1.7 (tv topology eq coordinates).**

$$\forall s: ActivePhase, \operatorname{tvTopology}\left(s\right)=\operatorname{coordinateTopology}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_topology_eq_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every singleton real mass is Lipschitz with constant one for the actual TV distance. ENNReal singleton mass is the continuous ofReal image of that real mass. Conversely, arbitrary probability laws admit finite sets with arbitrarily small complementary mass. The finite sum of coordinate discrepancies tends to zero in the coordinate topology. The event-supremum finite-coordinate estimate then places a coordinate neighborhood inside every TV ball. These two directions identify the topologies for all laws, including laws of infinite support.

**Theorem 1.8 (tv borel eq).**

$$\forall s: ActivePhase, \operatorname{Borel}\left(\operatorname{tvTopology}\left(s\right)\right)=\operatorname{Giry}\left(\operatorname{ProbabilityMeasure}\left(\operatorname{ValidTail}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_borel_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete-coordinate map is a measurable equivalence, and its target simplex has the inherited Borel structure of a countable ENNReal product. The established topology equality therefore identifies actual TV-Borel with the evaluation/Giry sigma algebra. No weak-convergence topology is substituted.

**Theorem 1.9 (descriptor tv borel eq).**

$$\forall s: ActivePhase, \operatorname{Borel}\left(\operatorname{descriptorTVTopology}\left(s\right)\right)=\operatorname{InheritedGiry}\left(\operatorname{RegularDescriptor}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.descriptor_tv_borel_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

descriptorTVTopology is the exact subspace TV topology on the unchanged Regular predicate. Subspace Borel transport gives its inherited measurable structure. Both phase marginals, the acquired kernels, full residuals and bounded real input tests can consequently use this same measurable carrier. The two full joint-test equivalences apply this identification to their original fixed joint laws and unweighted margins.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.coordinateEquiv`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.descriptor_tv_borel_eq`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.regular_infinity_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.regular_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.residualA_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.residualB_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_borel_eq`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_finite_coordinate_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelTVTopology.tv_topology_eq_coordinates`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow](NativeBorelCommonFlow.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks](NativePaidHistoryCommonRowRisks.md)
