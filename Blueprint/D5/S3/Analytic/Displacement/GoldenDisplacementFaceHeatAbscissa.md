# The Exact Golden Displacement Face Heat Abscissa

## Abstract

A nonnegative Euler bridge promotes summable positive prime-power tails to a global sum, and collapses the expansion-face heat window to the exact golden abscissa.

**Theorem 1.1 (Summable prime-power tails give a global sum).**

$$\forall f: \mathbb{N} \to \mathbb{R}, f(0)=0, f(1)=1, \forall n, 0\leq f(n), \forall m, n, \operatorname{Coprime}(m, n) \Rightarrow f(m\times n)=f(m)\times f(n), \operatorname{Summable}((p \text{prime}, k)\mapsto f(p^{k+1})) \Rightarrow \operatorname{Summable}(f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa.summable_of_summable_prime_power_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib's smooth-number Euler theorem computes every finite prime partial product. Nonnegativity turns the combined positive prime-power tail sum into a uniform exponential bound for those partial products, while every positive natural eventually lies in a smooth-number set. Bounded monotone finite sums therefore give global summability.

**Theorem 1.2 (The face heat abscissa is exactly one over phi squared).**

$$\operatorname{IsHeatAbscissa}(faceLength, \frac{1}{\varphi^{2}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa.faceLength_heat_abscissa_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one over phi squared, the frozen golden-spectrum theorem makes the complete positive prime-power tail summable. The bridge then sums the real displacement coefficients globally, and their closed form is the face heat family. The frozen face divergence theorem supplies the opposite half-plane, so the former bracket collapses to equality.

## References

- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa.faceLength_heat_abscissa_exact`
- Truth anchor: `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa.summable_of_summable_prime_power_tail`
- Dependency: [D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatTrace](GoldenDisplacementFaceHeatTrace.md)
