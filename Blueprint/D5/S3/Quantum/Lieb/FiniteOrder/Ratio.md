# Monotonicity of the zero-extended ratio

## Abstract

Monotonicity of the zero-extended ratio

For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite.

**Theorem 1.1 (Ratio monotonicity on the open positive cone).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land (\forall t \in \mathbb{R},\; (0<t) \Rightarrow (0<\operatorname{apply}\left(f, t\right)))) \land ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land ((\operatorname{PosDef}\left(A\right)) \land ((\operatorname{PosDef}\left(B\right)) \land (A \le B))))) \Rightarrow (\operatorname{cfc}\left(\operatorname{zeroExtendedRatio}\left(f\right), A\right) \le \operatorname{cfc}\left(\operatorname{zeroExtendedRatio}\left(f\right), B\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrder/Ratio.ratio_monotone_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite A <= B, set C=B^(-1/2) A^(1/2). Its contraction inequality and doubled-order Jensen show that f(t)/t is matrix antitone. Each spectral value of this normalized function is strictly positive. Order reversal under inversion and the finite spectral inverse identity therefore show that t/f(t) is matrix monotone at order n. This is the normalized-inverse argument of Hoa, Osaka and Toan, Proposition 2.1; the hypotheses allow f(0)=0 because A and B are positive definite.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrder/Ratio.ratio_monotone_posDef`
- Dependency: [D5/S3/Quantum/Lieb/FiniteOrderCompression](../FiniteOrderCompression.md)
