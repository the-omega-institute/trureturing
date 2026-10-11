# Coordinates and full residuals

## Abstract

Complete legal-law representation

ProbabilityMeasure(ValidTail(s)) is the existing probability-law carrier, and Regular is exactly the source emission interval and all source tail bounds. Infinity remains in ValidTail and in every coordinate comparison. Simplex(s) consists of all ENNReal coordinate functions with countable sum one. No finite-support condition is imposed.

**Definition 1.1 (coordinateEquiv).**

$$\forall s: ActivePhase, \operatorname{MeasurableEquiv}\left(\operatorname{coordinateEquiv}\left(s\right), \operatorname{ProbabilityMeasure}\left(\operatorname{ValidTail}\left(s\right)\right), \operatorname{Simplex}\left(s\right)\right)$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.coordinateEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map takes every singleton mass. The inverse is the countable sum of mass(t) times Dirac(t). Singleton reconstruction proves both inverse identities, and measurable evaluation and countable sums prove measurability in both directions. This identifies Giry with complete-coordinate measurability. The complete-coordinate topology theorem uses this equivalence and the finite TV estimate to identify the original TV topology and Borel sets for all laws.

**Theorem 1.2 (regular measurable).**

$$\forall s: ActivePhase, \operatorname{MeasurableSet}\left(\operatorname{RegularSet}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.regular_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RegularSet(s) is the set of probability laws D satisfying Regular(s,D), with the unchanged interval [1/3,2/5], tail rate 4/15, and suspended tail factor 2/5. Each inequality is measurable and the intersection is countable. The explicit simplex equivalence transports standard-Borel structure to probability laws; this measurable regularity set then gives the original RegularDescriptor subtype standard-Borel structure.

**Theorem 1.3 (regular infinity zero).**

$$\forall s: ActivePhase, \forall D: RegularDescriptor, \operatorname{mass}\left(\operatorname{law}\left(D\right), \operatorname{infinity}\left(s\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.regular_infinity_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D ranges over RegularDescriptor(s). Every tailSet(s,j) contains infinity. Its mass bounds that singleton and tends to zero, including the suspended factor. Infinity is retained as a coordinate; its zero mass is derived from regularity.

**Theorem 1.4 (residualB measurable).**

$$\operatorname{Measurable}\left(\operatorname{residualB}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.residualB_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

residualB maps PDescriptor into the entire measure space on ValidTail(beta). The range of prependB is the complement of the first alpha atom. Its comap mass is exactly 1-u, so the normalized residual is a probability measure. The reciprocal is finite because 3/5 <= 1-u <= 2/3. No opposite regularity premise is used.

**Theorem 1.5 (residualA measurable).**

$$\operatorname{Measurable}\left(\operatorname{residualA}\left(\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.residualA_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

residualA maps BDescriptor into the entire measure space on ValidTail(p). The range of prependA is the complement of betaStop. Its comap mass is v and 1/3 <= v <= 2/5, so normalization gives a probability measure. Comap evaluation and the same original input emission give measurability.

**Theorem 1.6 (tv finite coordinate bound).**

$$\forall s: ActivePhase, \forall P: ProbabilityMeasureValidTail, \forall Q: ProbabilityMeasureValidTail, \forall F: FinsetValidTail, \operatorname{TV}\left(P, Q\right)\leq\operatorname{ofReal}\left(\operatorname{finiteCoordinateGapPlusTail}\left(P, Q, F\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.tv_finite_coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P and Q range over all probability laws on ValidTail(s), and F is any finite set of complete atoms. finiteCoordinateGapPlusTail means sum over t in F of abs[P.real{t}-Q.real{t}] plus P.real(complement F). TV is exactly the repository event-supremum of the maximum of the two ENNReal directed differences. Split an event over F and its complement; the reverse difference follows by applying the same bound to the complementary event and using both total masses equal to one. This establishes the finite-coordinate TV neighborhood estimate without assuming a weak-topology identification. Finite approximation and both neighborhood directions establish the corresponding topology and Borel equality in NativeBorelTVTopology.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.coordinateEquiv`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.regular_infinity_zero`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.regular_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.residualA_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.residualB_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.tv_finite_coordinate_bound`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelCommonFlow](NativeBorelCommonFlow.md)
