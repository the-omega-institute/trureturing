# Whole Dependent Fiber Form

## Abstract

A whole type is canonically equivalent to the dependent sum of the fibers of any coordinate readout.

**Theorem 1.1 (Whole dependent fiber form).**

$$\forall X, B: \operatorname{Type}, q: X \to B,\ \operatorname{Nonempty}(X \equiv \sum _{b: B} R(b)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/WholeDependentFiberForm.whole_dependent_fiber_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary coordinate readout q : X -> B, the residual fiber over b consists of an object x together with an equality q(x) = b.

The equivalence sends each object to its coordinate and reflexive fiber witness, and recovers an object by forgetting those coordinates.

The statement quantifies over arbitrary types and an arbitrary readout. It requires no quotient object, surjectivity, section, linear structure, or metric, and its Lean axiom audit has no choice dependency.

The canonical Concept and ConceptFiber vocabulary is imported from the existing concept-fiber family, whose exact decomposition theorem is applied directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/WholeDependentFiberForm.whole_dependent_fiber_form`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
