# Canonical Dependent Fiber Equivalence

## Abstract

The canonical dependent-fiber equivalence records a readout and recovers its source.

**Theorem 1.1 (Canonical dependent-fiber equivalence).**

$$\forall X, B: \operatorname{Type}, q: X \to B, e_{q} := \operatorname{canonical}(q): X \equiv \sum _{b: B} \operatorname{ConceptFiber}\left(q, b\right), (\forall x: X, e_{q}(x) = \langle q(x), \langle x, refl\rangle\rangle) \land (\forall b: B, x: X, p: q(x) = b, e_{q}^{-1}(\langle b, \langle x, p\rangle\rangle) = x).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence.whole_dependent_fiber_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any readout q : X -> B, the named equivalence e_q sends x to its coordinate q(x), the same object x, and the reflexive proof that x lies in that fiber.

The inverse computation is public as well: it recovers x by forgetting the coordinate and equality witness.

No quotient, surjectivity, section, linear structure, or metric is assumed. The construction uses the pinned natural fiber equivalence directly, and its axiom audit has no choice dependency.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence.whole_dependent_fiber_form`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../ConceptFiberDecomposition.md)
