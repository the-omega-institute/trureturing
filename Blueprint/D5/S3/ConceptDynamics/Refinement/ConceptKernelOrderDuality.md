# Concept Classes and Kernel Relations

## Abstract

Effective concept classes are dual to source equivalence relations.

**Theorem 1.1 (Effective concept classes are order-dual to kernel relations).**

$$\begin{gathered}\forall X: \operatorname{Type},\\{}\operatorname{Bijective}(\operatorname{conceptClassKernel}(X)) \land\\{}(\forall C, D \in \operatorname{EffectiveConcept}(X), \operatorname{Refines}(q_{C}, q_{D}) \iff \operatorname{ker}(q_{D}) \subseteq \operatorname{ker}(q_{C})) \land\\{}(\forall C, D: \operatorname{Type}, q_{C}: \operatorname{Concept}(X, C), q_{D}: \operatorname{Concept}(X, D), \operatorname{ker}(\operatorname{conceptJoin}(q_{C}, q_{D})) = \operatorname{intersection}(\operatorname{ker}(q_{C}), \operatorname{ker}(q_{D}))) \land\\{}(\forall C, D: \operatorname{Type}, q_{C}: \operatorname{Concept}(X, C), q_{D}: \operatorname{Concept}(X, D), \operatorname{ker}(\operatorname{commonCoarsening}(q_{C}, q_{D})) = \operatorname{EqvClosure}(\operatorname{union}(\operatorname{ker}(q_{C}), \operatorname{ker}(q_{D})))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.concept_kernel_order_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An effective concept presentation consists of a readout together with surjectivity onto its coordinate carrier. Mutual refinement is the antisymmetrization of the canonical factor-map preorder.

The kernel map sends each resulting concept class to the equality relation induced on its source. It is publicly bijective, and a coarse concept refines through a finer one exactly when the finer kernel is contained in the coarse kernel.

The final two public conjuncts use the canonical family join and the quotient projection for common coarsening. Their kernels are, respectively, the relation intersection and the equivalence closure of the relation union.

The proof directly applies the pinned antisymmetrization and setoid lattice constructions. Surjectivity supplies representatives for the reverse kernel-to-factorization implication.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality.concept_kernel_order_duality`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
