# Normalized exponential remainder orders

## Abstract

Original Mills normalization and complete classification.

**Theorem 1.1 (The exact normalized Taylor remainder integral).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.normalized_exp_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.normalized_exp_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural r and y>0, the signed remainder divided by y^(r+1) equals the integral of (1-s)^r exp(-sy) over [0,1], divided by r!. The original remainder and its normalization are retained.

**Theorem 1.2 (Strictly decreasing upper normalized remainder).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_anti`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_anti` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write E_k(y) = (-1)^k (exp(-y) - sum_{j<k} (-y)^j/j!). For every k >= 1, E_k(y)/y^k strictly decreases on y > 0. The proof uses the existing public ExpRemainderDifferences.R with k=r+1, then the pinned Mathlib Taylor integral theorem gives E_k(y)/y^k = integral_0^1 (1-s)^(k-1) exp(-sy) ds / (k-1)!. Strict integral comparison at s=1/2 proves the multiplier order.

**Theorem 1.3 (Strictly increasing lower normalized remainder).**

Lean statement: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k >= 1, E_k(y)/y^(k-1) strictly increases on y > 0. Changing variables in the same Taylor integral gives E_k(y)/y^(k-1) = integral_0^y (1-q/y)^(k-1) exp(-q) dq / (k-1)!. Increasing y increases the integrand on the old interval and adds a strictly positive interval. This includes k=1.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_anti`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.exp_remainder_ratio_strict_mono`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/NormalizedRemainderOrders.normalized_exp_remainder`
- Dependency: [D5/S3/Analytic/XuYangMillsRemainder/Result](Result.md)
