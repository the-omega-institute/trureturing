# Noisy Moment Phase Boundary

## Abstract

Every feasible exterior mass satisfies the affine noisy-moment bound, whose equality case has a unique probability pair.

**Theorem 1.1 (Affine bound and exact equality classification).**

Lean statement: `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct real nodes and an off-node point, the Lagrange 0/1 dual polynomial determines P, the coefficient cost L, the signed perturbation r, and transition slopes A_i=P*r_i/c_i-L. Every normalized nonnegative feasible triple has a nonnegative dual gap 1+epsilon*L-w*P, equal to the sum of its nodal and noisy-coordinate slacks; in particular, w*P is at most 1+epsilon*L. If every nonconstant dual coefficient is nonzero, equality holds exactly when every epsilon*A_i is at most one and the two probability weights are the computed positive and negative parts. The equality decomposition forces each noisy moment to saturate and then forces every nodal weight, while the converse construction verifies normalization and all moments. Equality at a transition constraint is included. The result classifies attainment of this affine bound; it makes no assertion about later optimal phases or zero dual coefficients.

## References

- Truth anchor: `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](GoldenTomography/FinitePronyHankelReconstruction.md)
