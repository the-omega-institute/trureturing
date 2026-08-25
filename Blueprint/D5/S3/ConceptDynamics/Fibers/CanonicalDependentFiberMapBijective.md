# Canonical Dependent Fiber Map Bijective

## Abstract

The canonical map into the dependent sum of readout fibers is bijective.

**Theorem 1.1 (The canonical dependent-fiber map is bijective).**

$$\forall X, B: \operatorname{Type}, q: X \to B, \operatorname{Bijective}(x \mapsto \langle q(x), \langle x, refl\rangle\rangle: X \to \sum _{b: B} \sum _{y: X} q(y) = b).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberMapBijective.canonical_dependent_fiber_map_bijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any readout q : X -> B, the map records q(x), the object x, and the reflexive proof that x belongs to that fiber.

The frozen family equivalence supplies both injectivity and surjectivity without a quotient, section, or choice hypothesis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberMapBijective.canonical_dependent_fiber_map_bijective`
- Dependency: [D5/S3/ConceptDynamics/Fibers/CanonicalDependentFiberEquivalence](CanonicalDependentFiberEquivalence.md)
