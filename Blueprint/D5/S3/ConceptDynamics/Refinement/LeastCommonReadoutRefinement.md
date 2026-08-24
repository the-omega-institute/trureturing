# Least Common Readout Refinement

## Abstract

The canonical joint readout is the least common refinement and realizes kernel intersection.

**Theorem 1.1 (The joint readout is the least common refinement).**

$$\begin{gathered}\forall X, C, D: \operatorname{Type},\\{}q_{J}: X \to C, q_{K}: X \to D,\\{}\operatorname{Refines}\left(q_{J}, \operatorname{conceptJoin}\left(q_{J}, q_{K}\right)\right) \land\\{}\operatorname{Refines}\left(q_{K}, \operatorname{conceptJoin}\left(q_{J}, q_{K}\right)\right) \land\\{}(\forall E: \operatorname{Type}, q_{E}: X \to E, \operatorname{Refines}\left(q_{J}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(q_{K}, q_{E}\right) \Rightarrow \operatorname{Refines}\left(\operatorname{conceptJoin}\left(q_{J}, q_{K}\right), q_{E}\right)) \land\\{}\operatorname{ker}\left(\operatorname{conceptJoin}\left(q_{J}, q_{K}\right)\right) = \operatorname{intersection}\left(\operatorname{ker}\left(q_{J}\right), \operatorname{ker}\left(q_{K}\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/LeastCommonReadoutRefinement.least_common_readout_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The readouts q_J and q_K share an arbitrary source X. Their joint readout is the canonical conceptJoin, which records the pair of component values without introducing a second join primitive.

The first two public conjuncts are the projection refinements. The third quantifies over every competing readout and states the universal factorization through any common refinement.

The final public conjunct identifies the joint kernel with the intersection of the component kernels. This is the relation used by the repository's canonical quotient construction.

Both results are direct applications of the frozen concept-family universal property and kernel-order duality theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/LeastCommonReadoutRefinement.least_common_readout_refinement`
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](ConceptKernelOrderDuality.md)
