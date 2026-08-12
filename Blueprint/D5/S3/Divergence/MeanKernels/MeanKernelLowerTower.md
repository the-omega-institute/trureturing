# The Lower Reciprocal-Mean Tower

## Abstract

The logarithmic-mean reciprocal kernel is bounded above by the geometric, harmonic and squared-geometric reciprocal kernels.

**Theorem 1.1 (The logarithmic-mean kernel is bounded above by the geometric, harmonic and squared-geometric kernels).**

$$\forall a,b, 0<a \Rightarrow 0<b \Rightarrow a\neq b \Rightarrow a+b\le2 \Rightarrow\\\frac{\log a-\log b}{a-b}\le \frac{1}{\sqrt{ab}}\le \frac{a^{-1}+b^{-1}}{2}\le \frac{1}{ab}$$

*Proof.* Machine-checked in Lean as `D5/S3/Divergence/MeanKernels/MeanKernelLowerTower.mean_kernel_lower_tower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct positive reals a and b whose sum is at most 2, the reciprocal kernel of the logarithmic mean, (log a − log b)/(a − b), is bounded above in turn by the reciprocal kernel of the geometric mean, 1/√(ab), the reciprocal kernel of the harmonic mean, (a⁻¹ + b⁻¹)/2, and the reciprocal kernel of the squared geometric mean, 1/(ab). Inverting the kernels, this is the mean chain H(a,b) ≤ G(a,b) ≤ L(a,b) of the harmonic, geometric and logarithmic means, together with the endpoint G(a,b)² ≤ H(a,b), which holds exactly when a + b ≤ 2.

The two scale-invariant steps reduce to a one-variable inequality in u = √(a/b) ≥ 1 (taken by symmetry of the kernels under exchanging a and b). The geometric–logarithmic step G ≤ L is 2u·log u ≤ u² − 1, i.e. log u ≤ (u − 1/u)/2, which is the statement that a real number is at most its hyperbolic sine, applied at log u ≥ 0. The harmonic step H ≤ G is the arithmetic–geometric mean inequality 2√(ab) ≤ a + b. The endpoint G² ≤ H, by contrast, is scale-dependent: (a⁻¹ + b⁻¹)/2 ≤ 1/(ab) rearranges directly to a + b ≤ 2.

This is not a restatement of a library lemma: a search of Mathlib finds the logarithm quotient and power laws, the arithmetic–geometric mean inequality, and the sine-hyperbolic bound, but no logarithmic mean, no geometric–logarithmic mean inequality G ≤ L, and no assembled reciprocal-kernel chain. Only the lower portion of the reciprocal-mean tower is claimed here: the top link 2/(a + b) ≤ (log a − log b)/(a − b) (the L ≤ A step) is recorded in the sibling logarithmic-mean sandwich and is not restated, and the operator divergence tower over density matrices that this scalar chain drives is not covered.

## References

- Truth anchor: `D5/S3/Divergence/MeanKernels/MeanKernelLowerTower.mean_kernel_lower_tower`
