# Local Descent and Global Gluing Compatibility

## Abstract

Finite local descent requires separate transition, inverse-limit image, and cocycle checks before it becomes a compatible global descent.

**Definition 1.1 (Natural numbers form a tower of finite truncations).**

$$\forall n, \operatorname{Coordinate}\left(truncatedNaturalSystem, n\right) = \operatorname{Fin}\left(n+1\right), \forall x\in \mathbb{N}, \operatorname{readout}\left(truncatedNaturalSystem, n, x\right) = \operatorname{min}\left(x, n\right), \forall y\in \operatorname{Fin}\left(n+2\right), \operatorname{restrict}\left(truncatedNaturalSystem, n, y\right) = \operatorname{min}\left(y, n\right).$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.truncatedNaturalSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At level n the coordinate carrier is Fin(n+1). A natural number is read as its minimum with n, and restriction to the preceding level truncates once more. The minimum identities supply the transition laws.

**Definition 1.2 (The maximal finite coordinates form a compatible thread).**

$$\forall n\in \mathbb{N}, \operatorname{escapingThread}\left(n\right) = n.$$

*Formalization.* `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.escapingThread` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The thread selects the largest element n at level n. Restriction sends the largest element at level n+1 to the largest element at level n.

**Lemma 1.3 (Every finite truncation is realized).**

$$\forall n\in \mathbb{N}, \operatorname{Surjective}\left(\operatorname{readout}\left(truncatedNaturalSystem, n\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.every_finite_readout_is_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coordinate y in Fin(n+1) is realized by the natural number y itself, because truncating y at n leaves it unchanged.

**Lemma 1.4 (The compatible maximal thread has no global realization).**

$$escapingThread \neg\in \operatorname{range}\left(\operatorname{stateThread}\left(truncatedNaturalSystem\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.escaping_thread_not_in_global_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a natural number x realized the thread, its coordinate at level x+1 would have to equal both x and x+1. Thus levelwise realizability does not imply membership in the global state-thread image.

**Theorem 1.5 (Local closure leaves three global gluing obligations).**

$$[\forall c, \operatorname{incompatibleWitnessLocalValue}\left(c, \operatorname{witnessAtomSupport}\left(c\right)\right) = 1 \land \operatorname{IsContextwiseAdditive}\left(witnessEventSupport, IsDisjointUnion, incompatibleWitnessLocalValue\right) \land \neg \exists globalValue: \operatorname{CoveredEvent}\left(witnessEventSupport\right) \to \mathbb{R}, \operatorname{RestrictsToContexts}\left(witnessEventSupport, incompatibleWitnessLocalValue, globalValue\right)] \land [\forall n, \operatorname{Surjective}\left(\operatorname{readout}\left(truncatedNaturalSystem, n\right)\right) \land escapingThread \neg\in \operatorname{range}\left(\operatorname{stateThread}\left(truncatedNaturalSystem\right)\right)] \land [\forall Index, Base, UnitGroup: \operatorname{Type}, [\operatorname{Group}\left(UnitGroup\right)], overlap: Index \to Index \to Base \to \operatorname{Prop}, transition: Index \to Index \to Base \to UnitGroup, (\exists globalFrameCoefficients: Index \to Base \to UnitGroup, \forall i, j, x, \operatorname{overlap}\left(i, j, x\right) \Rightarrow \operatorname{globalFrameCoefficients}\left(i, x\right) = \operatorname{transition}\left(i, j, x\right) \cdot \operatorname{globalFrameCoefficients}\left(j, x\right)) \iff (\exists localUnit: Index \to Base \to UnitGroup, \forall i, j, x, \operatorname{overlap}\left(i, j, x\right) \Rightarrow \operatorname{transition}\left(i, j, x\right) = \operatorname{inverse}\left(\operatorname{localUnit}\left(i, x\right)\right) \cdot \operatorname{localUnit}\left(j, x\right))].$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.local_descent_requires_global_gluing_checks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first public clause reuses the frozen two-chart witness: each chart is normalized and additive, but disagreement on their shared event precludes a global restriction. This is an explicit local-to-global countermodel, not a converse hidden in a premise.

The second clause exposes the independent inverse-limit image check via the finite truncation tower. The third reuses the frozen criterion that transition-compatible global coefficients exist exactly when the unit-valued transition cocycle is a coboundary.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.escapingThread`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.escaping_thread_not_in_global_image`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.every_finite_readout_is_surjective`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.local_descent_requires_global_gluing_checks`
- Truth anchor: `D5/S3/ConceptDynamics/Gluing/LocalDescentGlobalCompatibility.truncatedNaturalSystem`
- Dependency: [D5/S3/ConceptDynamics/Gluing/GlobalFrameCoboundaryCriterion](GlobalFrameCoboundaryCriterion.md)
- Dependency: [D5/S3/QuantumContext/PublicLedgerDescent](../../QuantumContext/PublicLedgerDescent.md)
