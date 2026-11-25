# Monotonicity of the zero-extended ratio

## Abstract

Monotonicity of the zero-extended ratio

For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite.

**Theorem 1.1 (Ratio monotonicity on the closed positive cone).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land (\forall t \in \mathbb{R},\; (0<t) \Rightarrow (0<\operatorname{apply}\left(f, t\right)))) \land ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land ((\operatorname{PosSemidef}\left(A\right)) \land ((\operatorname{PosSemidef}\left(B\right)) \land (A \le B))))) \Rightarrow (\operatorname{cfc}\left(\operatorname{zeroExtendedRatio}\left(f\right), A\right) \le \operatorname{cfc}\left(\operatorname{zeroExtendedRatio}\left(f\right), B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio.ratio_monotone_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ratio is monotone on the entire positive semidefinite cone, including a zero eigenvalue and functions vanishing at zero. First replace f by f+epsilon. A positive scalar shift of A and B permits the positive-definite ratio theorem; continuity of the regularized ratio then removes that shift. Finally epsilon tends to zero. On each fixed finite spectrum, the value at zero is identically zero and every positive spectral point has f(t)>0, so pointwise convergence suffices. Continuity of the original ratio at zero is not required.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio.ratio_monotone_posSemidef`
- Dependency: [D5/S3/Quantum/Lieb/FiniteOrder/Ratio](Ratio.md)
