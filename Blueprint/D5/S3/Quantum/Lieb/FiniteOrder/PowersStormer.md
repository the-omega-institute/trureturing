# The finite-order generalized Powers-Stormer inequality

## Abstract

The finite-order generalized Powers-Stormer inequality

For every natural number n, MatrixMonotone(n,f) means that cfc(f,X) <= cfc(f,Y) for all positive semidefinite complex n by n matrices X <= Y. The calculus is the actual finite spectral functional calculus, and ReTr is the unnormalized real trace. zeroExtendedRatio(f) sends t to t/f(t), using total division, so its value at zero is zero. No continuity of this quotient at zero is implicit in the notation. Zero dimensions and singular noncommuting matrices are included wherever positivity is semidefinite. The hypotheses on f are continuity on [0,infinity) and f(t)>0 for every t>0. Right continuity then gives f(0)>=0. The trace norm is ReTr(sqrt(M* M)); it is not divided by the dimension or by two.

**Theorem 1.1 (The full singular trace inequality).**

$$\forall n \in \mathbb{N}, f \in \mathbb{R} \to \mathbb{R}, A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right), B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (((\operatorname{ContinuousOn}\left(f, \operatorname{Ici}\left(0\right)\right)) \land (\forall t \in \mathbb{R},\; (0<t) \Rightarrow (0<\operatorname{apply}\left(f, t\right)))) \land ((\operatorname{MatrixMonotone}\left(2 \cdot n, f\right)) \land ((\operatorname{PosSemidef}\left(A\right)) \land (\operatorname{PosSemidef}\left(B\right))))) \Rightarrow (\operatorname{ReTr}\left(A\right) + \operatorname{ReTr}\left(B\right) - \operatorname{traceNorm}\left(A - B\right) \le 2 \cdot \operatorname{ReTr}\left(\operatorname{sqrt}\left(\operatorname{cfc}\left(f, A\right)\right) \cdot \operatorname{cfc}\left(\operatorname{zeroExtendedRatio}\left(f\right), B\right) \cdot \operatorname{sqrt}\left(\operatorname{cfc}\left(f, A\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Lieb/FiniteOrder/PowersStormer.generalized_powers_stormer` (`✓ std3`). ∎

*Citation.* Dinh Trung Hoa; Hiroyuki Osaka; Ho Minh Toan (2012). *On generalized Powers-Størmer's Inequality*. DOI: [10.48550/arXiv.1204.6665](https://doi.org/10.48550/arXiv.1204.6665). URL: <https://arxiv.org/html/1204.6665v1>.

*Commentary.*

Hoa, Osaka and Toan, Theorem 2.1, gives this inequality with factor two for the unnormalized canonical trace. Take the single common upper bound C=B+posPart(A-B)=A+negPart(A-B). Both f and its zero-extended ratio are monotone at order n. Positivity of trace pairings, the identities f(X)g(X)=X and a common-roof estimate yield ReTr(A)-(ReTr(C)-ReTr(B)) <= ReTr(f(A)g(B)). The Jordan trace-norm identity converts the left side into half the asserted trace deficit. Trace cyclicity converts the crossed product to the displayed positive sandwich. The construction keeps the same C in every comparison and requires neither commutativity nor invertibility.

## References

- Truth anchor: `D5/S3/Quantum/Lieb/FiniteOrder/PowersStormer.generalized_powers_stormer`
- Dependency: [D5/S3/Quantum/Lieb/FiniteOrder/SingularRatio](SingularRatio.md)
- Dependency: [D5/S3/Quantum/Matrix/Spectral/TraceNorm](../../Matrix/Spectral/TraceNorm.md)
- Dependency: [D5/S3/Quantum/Matrix/Spectral/TraceOrder](../../Matrix/Spectral/TraceOrder.md)
