# The Logarithmic-Mean Kernel Sandwich

## Abstract

The logarithmic-mean kernel lies between the arithmetic and harmonic reciprocal kernels.

**Theorem 1.1 (The logarithmic-mean kernel lies between the arithmetic and harmonic kernels).**

$$\forall a,b, 0<a \Rightarrow 0<b \Rightarrow a\neq b \Rightarrow\\\frac{2}{a+b}\le \frac{\log a-\log b}{a-b}\le \frac{a^{-1}+b^{-1}}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich.logMean_kernel_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct positive reals a and b, the reciprocal kernel of the logarithmic mean, (log a − log b)/(a − b), lies between the reciprocal kernel of the arithmetic mean, 2/(a + b), and the reciprocal kernel of the harmonic mean, (a⁻¹ + b⁻¹)/2. Inverting the three kernels, this is exactly the classical chain of harmonic, logarithmic and arithmetic means, H(a,b) ≤ L(a,b) ≤ A(a,b).

The proof reduces each bound to a one-variable inequality in the ratio t = a/b (taken at least one by symmetry of the three kernels under exchanging a and b). The upper bound is 2(t − 1)/(t + 1) ≤ log t, obtained from the monotonicity of s ↦ log s − 2(s − 1)/(s + 1) on the ray from one, whose derivative (s − 1)²/(s(s + 1)²) is nonnegative. The lower bound is log t ≤ (t − 1/t)/2, which is the statement that a real number is at most its hyperbolic sine, applied at log t ≥ 0.

This is not a restatement of a library lemma: a search of Mathlib finds the logarithm quotient and product laws, monotonicity from a nonnegative derivative, and the sine-hyperbolic bound, but no logarithmic mean and no assembled kernel sandwich. The chain is the load-bearing ordering behind the corresponding path-divergence comparison; only the mean-kernel sandwich itself is claimed here, not the integral path-divergence ordering it implies.

## References

- Truth anchor: `D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich.logMean_kernel_sandwich`
