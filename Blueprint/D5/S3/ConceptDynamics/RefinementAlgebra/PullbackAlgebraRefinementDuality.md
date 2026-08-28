# Refinement and the Pullback Algebra

## Abstract

Realized-image refinement is dual to kernels and the canonical pullback algebra.

**Theorem 1.1 (Refinement, kernels, and pullback algebras are equivalent).**

$$\forall X, O, P: \operatorname{Type},\\{}q: X \to O, r: X \to P,\\{}(\operatorname{Refines}(\operatorname{rangeFactorization}(q), \operatorname{rangeFactorization}(r)) \iff \operatorname{ker}(r) \subseteq \operatorname{ker}(q)) \land\\{}(\operatorname{ker}(r) \subseteq \operatorname{ker}(q) \iff \operatorname{PullbackAlgebra}(q) \subseteq \operatorname{PullbackAlgebra}(r)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality.pullback_algebra_refinement_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pullback algebra is the repository's canonical family of proposition-valued observables that factor through a readout.

Both readouts are normalized to their realized images before factorization is tested. The effective-image kernel theorem supplies the first equivalence.

Reverse kernel inclusion transports every observable from the coarser readout to the finer one. Conversely, equality with one selected coarse readout value constructs an observable that separates any pair distinguished by the coarse readout.

Body-shape search found the pullback-algebra owner in the imported deterministic-interface module. No duplicate event-algebra definition is introduced here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality.pullback_algebra_refinement_duality`
- Dependency: [D5/S3/ConceptDynamics/Dialectics/DeterministicInterfaceEquivalence](../Dialectics/DeterministicInterfaceEquivalence.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
