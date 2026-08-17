# Complementary Context Probability Pythagoras

## Abstract

Orthogonal context coordinates split matrix purity excess into observed probability deviations and complementary residual mass.

**Theorem 1.1 (Probability deviations and residual mass split purity).**

$$\operatorname{ProjectionCoordinates}(\rho, p, S) \Rightarrow\\\operatorname{ReTr}(\rho^{2}) - \frac{1}{d} =\\\sum_{l} \sum_{j} {p_{lj}-\frac{1}{d}}^{2} + r_S^{2}(\rho).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras.complementary_context_probability_pythagoras` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a finite complex matrix, let its centered Hermitian part be represented by a vector in a real Hilbert space, let p(l,j) be real probability coordinates, and let S be the visible coordinate subspace. Assume the squared norm of the centered state is the real trace purity excess and the squared norm of its projection to S is the double sum of squared centered probabilities.

The residual mass is defined as the squared norm of the projection to the orthogonal complement of S. Mathlib's exact orthogonal-projection Pythagoras theorem then gives the displayed equality without expanding matrix entries.

For pairwise mutually unbiased basis contexts, the two bridge assumptions are precisely the preceding centered-state and orthogonal-coordinate calculations. The result retains every context and outcome in the double sum; it does not specialize the identity to a single basis or a fixed matrix dimension.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/ComplementaryContextProbabilityPythagoras.complementary_context_probability_pythagoras`
