# Projective Interior Probability Fibers

## Abstract

Squared amplitudes on complex projective space have torus-shaped interior fibers.

**Theorem 1.1 (Interior projective probability fibers are tori).**

$$\forall n\in \mathbb{N}, p\in \operatorname{int}(\Delta_{n}),\\{}(\forall i, p_{i} > 0) \Rightarrow\\{}\operatorname{Bijective}(\operatorname{relativePhaseCoordinates}\left(p\right): \{[psi]\in CP^{{n}} \mid q_{B}([psi]) = p\} \to T^{{n}}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber.projective_interior_probability_fiber_equiv_torus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the standard basis on the complex vector space with n plus one coordinates. The public state carrier is its Mathlib projectivization, and the basis-probability map sends any nonzero representative to its coordinatewise squared amplitudes divided by their total.

For a strictly positive probability vector, every representative in the fiber has nonzero coordinates. Scaled affine ratios against coordinate zero therefore have squared norm one and define n relative circle phases.

The inverse uses amplitudes whose positive magnitudes are the square roots of the prescribed probabilities, fixes the reference phase to one, and inserts the n relative phases. Direct representative computations prove both inverse laws on the projective fiber.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber.projective_interior_probability_fiber_equiv_torus`
- Dependency: [D5/S3/Quantum/Fibers/InteriorProbabilityPhaseFiber](InteriorProbabilityPhaseFiber.md)
