# The one-mode cubic bound

## Abstract

Nonnegativity of the one-mode cubic spectral deficit at every r ≥ 1.

**Theorem 1.1 (Nonnegativity of the one-mode deficit).**

Lean statement: `D5/S3/Quantum/Semigroups/WuOneModeCubic.one_mode_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuOneModeCubic.one_mode_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

The cubic coefficient is the p = 3 specialization of Wu v1, Theorem 3.1, eq. (3.4), with Gibbs ratio r = exp(β/3). It agrees with the coefficient in Remark 3.15, eqs. (3.54)–(3.55), including the tracial value 1/2 at r = 1. For every r ≥ 1, the exact spectral premise OneModeBound r says that oneModeDeficit r v w z is nonnegative for all 0 ≤ v ≤ w and −1 ≤ z ≤ 1, where z is the upper eigenvector’s Bloch coordinate.

For 0 < v < w, completing the square in z reduces the proof to a scalar function of t = w/v. Comparing secant slopes of a strictly convex function of log t gives the sign of the scalar derivative on either side of t = r, where the scalar function attains its minimum of zero. At r = 1 the comparison uses the tangent slope at log t = 0. Continuity of x log x extends the deficit bound to v = 0 and v = w, with v = w = 0 checked directly.

For r ≥ 1, a unitary two-mode frame U and spectrum (m, n, n, 1) with 0 ≤ m ≤ n ≤ 1, pass one_mode_bound hr as the OneModeBound r argument of repeated_middle_lower_bound. The weighted sum of the two Hölder gaps and the frame remainder are each nonnegative, and their sum lower-bounds sourceDeficit r U m n in these spectral coordinates.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuOneModeCubic.one_mode_bound`
- Dependency: [D5/S3/Quantum/Semigroups/WuRepeatedMiddleCubic](WuRepeatedMiddleCubic.md)
