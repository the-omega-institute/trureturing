# Three Conditions of Entity Strength

## Abstract

Process stability, target fidelity, and nontrivial resolution are independent yet jointly realizable.

**Theorem 1.1 (The three entity-strength conditions are independent).**

$$\left(\exists c1 \in Bool \to Unit, t1 \in Bool \to Unit, P1 \in \operatorname{Set}\left(Bool \to Bool\right),\; \operatorname{ProcessStable}\left(P1, c1\right) \land \left(\operatorname{TargetFaithful}\left(t1, c1\right) \land \left(\neg \operatorname{NontrivialResolution}\left(c1\right)\right)\right)\right) \land \left(\left(\exists c2 \in Bool \times Bool \to Bool, t2 \in Bool \times Bool \to Bool, P2 \in \operatorname{Set}\left(Bool \times Bool \to Bool \times Bool\right),\; \operatorname{ProcessStable}\left(P2, c2\right) \land \left(\operatorname{NontrivialResolution}\left(c2\right) \land \left(\neg \operatorname{TargetFaithful}\left(t2, c2\right)\right)\right)\right) \land \left(\exists c3 \in Bool \to Bool, t3 \in Bool \to Bool, P3 \in \operatorname{Set}\left(Bool \to Bool\right),\; \operatorname{TargetFaithful}\left(t3, c3\right) \land \left(\operatorname{NontrivialResolution}\left(c3\right) \land \left(\neg \operatorname{ProcessStable}\left(P3, c3\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions.three_conditions_are_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

None of process stability, target fidelity, and nontrivial resolution follows from the other two. Three explicit concepts witness the three missing implications.

A constant Boolean-to-Unit concept is stable under every process and faithful to a constant target, but it distinguishes no states. On a Boolean pair, the first-coordinate concept is stable under all processes that preserve that coordinate and has nontrivial resolution, but it cannot recover the second-coordinate target.

Finally, the identity concept on Bool is faithful to the identity target and distinguishes false from true, while Boolean negation is an allowed process that violates stability.

**Lemma 1.2 (The three entity-strength conditions are jointly realizable).**

$$\exists c \in Bool \times Bool \to Bool, t \in Bool \times Bool \to Bool, P \in \operatorname{Set}\left(Bool \times Bool \to Bool \times Bool\right),\; \operatorname{ProcessStable}\left(P, c\right) \land \left(\operatorname{TargetFaithful}\left(t, c\right) \land \operatorname{NontrivialResolution}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions.three_conditions_jointly_realizable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the first coordinate of a Boolean pair satisfies all three conditions when the designated processes are exactly those that preserve that coordinate.

Preservation gives process stability directly, using the same first-coordinate readout as the target gives fidelity through the identity decoder, and pairs with different first coordinates supply nontrivial resolution.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions.three_conditions_are_independent`
- Truth anchor: `D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions.three_conditions_jointly_realizable`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
