# Noisy Moment Phase Boundary

## Abstract

The initial noisy-moment optimum has an exact support-transition boundary and a unique attaining probability pair.

**Theorem 1.1 (Exact attainment and rigidity at every noise level).**

Lean statement: `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct real nodes and an off-node point, the Lagrange 0/1 dual polynomial determines P, the coefficient cost L, the signed perturbation r, and transition slopes A_i=P*r_i/c_i-L. If every nonconstant dual coefficient is nonzero, a normalized nonnegative probability pair attains (1+epsilon*L)/P exactly when every epsilon*A_i is at most one and its weights equal the computed positive and negative parts. Necessity follows by decomposing the dual gap into nonnegative nodal and coordinate slacks, forcing each noisy moment to saturate and then forcing every nodal weight. Sufficiency constructs the normalized pair and verifies all moments. Equality at the first transition is included. This sharpens a sufficient small-noise radius into an exact boundary; it does not assume a pre-existing optimality or complementary-slackness witness. Later phases and zero dual coefficients are separate questions.

## References

- Truth anchor: `D5/S3/Analytic/NoisyMomentPhaseBoundary.exact_noise_phase_classification`
- Dependency: [D5/S3/Analytic/GoldenTomography/FinitePronyHankelReconstruction](GoldenTomography/FinitePronyHankelReconstruction.md)
