# Individual Rationality and Majority Cycles

## Abstract

Complete transitive individual rankings can aggregate into a nontransitive majority cycle with no faithful scalar order.

**Theorem 1.1 (Individually rational rankings produce a collective cycle).**

$$(\forall v \in \operatorname{Fin}\left(3\right), x \in \operatorname{Fin}\left(3\right), y \in \operatorname{Fin}\left(3\right), z \in \operatorname{Fin}\left(3\right),\; \left(\operatorname{prefers}\left(v, x, y\right) \land \operatorname{prefers}\left(v, y, z\right)\right) \Rightarrow \operatorname{prefers}\left(v, x, z\right)) \land \left((\forall v \in \operatorname{Fin}\left(3\right), x \in \operatorname{Fin}\left(3\right), y \in \operatorname{Fin}\left(3\right),\; \left(\neg x = y\right) \Rightarrow \left(\operatorname{prefers}\left(v, x, y\right) \lor \operatorname{prefers}\left(v, y, x\right)\right)) \land \left(\left(\operatorname{majorityPrefers}\left(0, 1\right) \land \left(\operatorname{majorityPrefers}\left(1, 2\right) \land \operatorname{majorityPrefers}\left(2, 0\right)\right)\right) \land \left(\left(\neg \operatorname{Transitive}\left(majorityPrefers\right)\right) \land \left(\neg \left(\exists u \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall x \in \operatorname{Fin}\left(3\right), y \in \operatorname{Fin}\left(3\right),\; \operatorname{majorityPrefers}\left(x, y\right) \Rightarrow u\left(x\right) > u\left(y\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Aggregation/IndividualRationalityMajorityCycle.individual_rationality_majority_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed profile ranks the three candidates cyclically across three voters. Every individual strict preference is transitive and complete on distinct candidates.

Pairwise counting makes zero beat one, one beat two, and two beat zero. Those public edges directly contradict transitivity of the majority relation, and the imported cycle obstruction excludes every faithful real-valued ordering.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Aggregation/IndividualRationalityMajorityCycle.individual_rationality_majority_cycle`
- Dependency: [D5/S3/ConceptDynamics/Aggregation/MajorityCycleNotScalarOrder](MajorityCycleNotScalarOrder.md)
