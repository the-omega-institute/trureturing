# Bounds and moments of the exact coefficients

## Abstract

Exact lacunary coefficients have summable weights and a divergent real second moment.

**Theorem 1.1 (Real and imaginary bounds for the reciprocal coefficient).**

Lean statement: `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.coefficient_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.coefficient_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real β and γ with 1/2 ≤ β ≤ 1 and γ ≥ 1, let ρ = β + iγ and c = 1/(ρ(1−ρ)). Then 1/(5γ²) ≤ Re(c) ≤ 1/γ² and |Im(c)| ≤ 1/γ³.

The real and imaginary parts of ρ(1−ρ) are x = γ²+β(1−β) and y = γ(1−2β). Thus γ² ≤ x ≤ 2γ² and |y| ≤ γ, giving γ⁴ ≤ x²+y² ≤ 5γ⁴. The real and imaginary parts of the reciprocal are x/(x²+y²) and −y/(x²+y²). The upper real bound uses x² ≤ x²+y².

**Theorem 1.2 (Summable weights and divergence of the real second moment).**

Lean statement: `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.weighted_summability`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.weighted_summability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let 1/2 ≤ β(n) ≤ 1 for all n in ℕ, let t ≥ 0, and set γ(n) = 3^(n+1). Use c(n) = 1/(ρ(n)(1−ρ(n))) with ρ(n) = β(n)+iγ(n). Write A(n) and B(n) for the real and imaginary parts of c(n) multiplied by exp((β(n)−1)t). Then A(n) ≥ 0 for all n. The families A(n), |B(n)|, and |B(n)γ(n)| are summable over ℕ, and A(n)γ(n)² is not summable.

The exponential factor is between exp(−t/2) and 1. The three summable families are bounded above by the geometric sequence γ(n)⁻². Every term A(n)γ(n)² is at least the positive constant exp(−t/2)/5. Also, at t = 2πm with m integral, γ(n)t = 2π times the integer 3^(n+1)m, so all frequencies have a common phase there.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.coefficient_bounds`
- Truth anchor: `D5/S3/Analytic/Asymptotics/ExactLacunaryCoefficients.weighted_summability`
