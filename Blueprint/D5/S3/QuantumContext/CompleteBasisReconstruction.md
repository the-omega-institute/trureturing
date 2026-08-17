# Complete Complementary-Basis Reconstruction

## Abstract

Complete complementary basis probabilities reconstruct a trace-one matrix.

**Theorem 1.1 (Complete complementary bases reconstruct the state).**

$$\rho = \frac{I}{d} + \sum_{\ell \in L} \sum_{j \in d} (p_{\ell j} - \frac{1}{d}) P_{j}^{\mathcal{B}_{\ell}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/CompleteBasisReconstruction.complete_basis_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P(l,j) be the rank-one outcome projectors of a complete family of pairwise mutually unbiased bases, and let p(l,j) be the real probability Tr(rho P(l,j)). Each basis resolves the identity, and the projector trace overlap is one on the same outcome, zero on different outcomes of one basis, and one over d across bases.

The completeness premise is the preceding tomography theorem's precise conclusion: equality of all selected projector traces determines the matrix. The proof evaluates the displayed candidate against every projector. Centered coefficients sum to zero within each basis, so all other-basis contributions cancel and the matching basis contributes exactly p(l,j).

Pinned Mathlib has no packaged mutually unbiased-basis reconstruction theorem. The proof directly applies its matrix sum, scalar, and trace identities. Positivity and Hermiticity of rho are not needed after the density-state trace-one condition and the real Born probabilities have been supplied.

## References

- Truth anchor: `D5/S3/QuantumContext/CompleteBasisReconstruction.complete_basis_reconstruction`
