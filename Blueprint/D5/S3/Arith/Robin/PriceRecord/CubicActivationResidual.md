# Cubic activation residual on prime prefixes

## Abstract

The cubic activation residual of the complete integer Robin infimum on prime prefixes.

**Theorem 1.1 (The scaled residual tends to (3/2)·3^(1/3)).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/CubicActivationResidual.integer_infimum_cubic_activation_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/CubicActivationResidual.integer_infimum_cubic_activation_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each natural cutoff P, let S be the primes at most P, H the sum of their logarithms, ell = log H, and λ = 1/(H·ell). The exact first activation sum A₁ is the sum over S of min(λ log p, p^(-2)). Then H^(2/3)·ell·(integerInfimum(S) − A₁) tends to (3/2)·3^(1/3) as P tends to infinity. The integer infimum is over the full image of the baseline-subtracted Robin objective for natural exponent vectors with exponents at least one on S.

The second activation sum uses min(λ log p, p^(-3)). For sufficiently large P it splits exactly at the real root t of t³ log t = H·ell. The head includes equality and the tail sums p^(-3) over t < p ≤ P. The root satisfies t/H^(1/3) → 3^(1/3), t → ∞, and P/t → ∞.

Finite Abel summation retains both prime-counting endpoints and the integral up to P. At scale t² log t, the upper endpoint tends to zero, the negative lower endpoint tends to −1, and the integral contribution tends to 3/2. The cubic tail therefore contributes 1/2 at that scale. The cutoff equation converts the scale exactly and the Chebyshev head contributes 3^(1/3).

The finite integer activation envelope uses radius 1/√H and trial cutoff H^(1/4). The established second-order limit places the infimum strictly below the radius, selecting the lower branch. Both envelope errors vanish at the cubic scale. Subtracting the exact first activation sum transfers the second activation limit to the full integer infimum.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/CubicActivationResidual.integer_infimum_cubic_activation_residual`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSecondOrder](IntegerInfimumSecondOrder.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimeBoundarySecondOrder](PrimeBoundarySecondOrder.md)
