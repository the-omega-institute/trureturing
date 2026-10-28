# The reciprocal Moebius sum

## Abstract

Every real prefix of the reciprocal Moebius sum has absolute value at most one.

**Definition 1.1 (The exact finite prefix).**

$$\forall x\in\mathbb{R},\operatorname{m}\left(x\right) = \sum_{1\le n\le \operatorname{floor}\left(x\right)}\frac{\operatorname{mu}\left(n\right)}{n}$$

*Formalization.* `D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound.reciprocalSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real cutoff x, m(x) sums the actual integer Moebius coefficients divided by their positive integer indices. The upper endpoint is the natural floor of x. The sum is empty when x is less than one, including negative x.

**Theorem 1.2 (A uniform bound at every real cutoff).**

$$\forall x\in\mathbb{R},\lvert \operatorname{m}\left(x\right)\rvert \le1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound.abs_reciprocalSum_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite divisor convolution gives the identity sum mu(n) floor(x/n)=1 for x at least one. Subtracting the integer parts from x m(x) leaves fractional parts. The absolute Moebius coefficient is at most one. Separating the index one leaves its exact fractional part x-floor(x), while the other floor(x)-1 terms are each at most one. Hence |x m(x)| is at most x, which proves the bound for positive x. Empty prefixes supply all remaining real cutoffs.

## References

- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound.abs_reciprocalSum_le_one`
- Truth anchor: `D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound.reciprocalSum`
