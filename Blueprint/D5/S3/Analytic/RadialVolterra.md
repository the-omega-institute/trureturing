# Radial Volterra bounds

## Abstract

Finite interval mass bounds control a scalar Volterra system with terminal data at infinity.

**Theorem 1.1 (Uniform amplitude and deviation bounds).**

Lean statement: `D5/S3/Analytic/RadialVolterra.norm_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/RadialVolterra.norm_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the positive half-line, let eta have derivative p with Re p ≥ 0, and let F and G solve F′ = p G and G′ = 2ν p G + q F with terminal limits one and zero. If the norm of q is bounded by a continuous nonnegative Q whose integral on each finite positive interval is at most V, with 0 ≤ V < ν, then |F(r)| ≤ ν/(ν−V) and |F(r)−1| ≤ V/(ν−V) for every r > 0. For each r the exponential integrating factor bounds the kernel by 1/ν. The terminal data and the mass bound control the error by V/ν times the supremum of |F| on the ray from r. Solving the supremum inequality gives both bounds.

## References

- Truth anchor: `D5/S3/Analytic/RadialVolterra.norm_bounds`
