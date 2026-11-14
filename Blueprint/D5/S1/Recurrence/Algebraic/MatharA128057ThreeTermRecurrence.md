# The A128057 square-root quotient

## Abstract

The three-term recurrence for the normalized square-root quotient A128057.

Work in ordinary formal power series Q[[X]]. There is a unique S with constant coefficient 1 and S²=1+4X². For every such S, its inverse is normalized and is a two-sided unit inverse. Set A=(1+X)S⁻¹ and a(n)=coeff n A. The formula below expands these two local definitions. Sequence indices are natural; subtraction inside a coefficient index is natural truncated subtraction. Every scalar polynomial, including 5n-9 and n-2, is evaluated in Q.

**Theorem 1.1 (The normalized root, its inverse, and the three-term recurrence).**

$$\left(\exists S \in \mathbb{Q}[[X]],\; \left(\operatorname{constantCoeff}\left(S\right) = 1 \land S^{2} = 1 + 4 \cdot X^{2}\right) \land \left(\forall R \in \mathbb{Q}[[X]],\; \left(\operatorname{constantCoeff}\left(R\right) = 1 \land R^{2} = 1 + 4 \cdot X^{2}\right) \Rightarrow R = S\right)\right) \land \left(\forall S \in \mathbb{Q}[[X]],\; \operatorname{constantCoeff}\left(S\right) = 1 \Rightarrow \left(S^{2} = 1 + 4 \cdot X^{2} \Rightarrow \left(\operatorname{constantCoeff}\left(S^{-1}\right) = 1 \land \left(S \cdot S^{-1} = 1 \land \left(S^{-1} \cdot S = 1 \land \left(\forall n \in \mathbb{N},\; 2 \le n \Rightarrow (n:\mathbb{Q}) \cdot (5 \cdot (n:\mathbb{Q}) - 9) \cdot \operatorname{coeff}\left(n, (1 + X) \cdot S^{-1}\right) + 4 \cdot \operatorname{coeff}\left(n - 1, (1 + X) \cdot S^{-1}\right) + 4 \cdot (5 \cdot (n:\mathbb{Q}) - 4) \cdot ((n:\mathbb{Q}) - 2) \cdot \operatorname{coeff}\left(n - 2, (1 + X) \cdot S^{-1}\right) = 0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a128057-three-term-recurrence` (proved) by `D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a128057-three-term-recurrence","declaration_gid":"D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Paul Barry; OEIS Foundation Inc. (2014). *OEIS A128057 — three-term recurrence for a square-root quotient*. URL: <https://oeis.org/A128057/internal>.

*Commentary.*

OEIS A128057 gives the generating function (1+x)/sqrt(1+4x²) and attributes the three-term conjecture to R. J. Mathar. Its offset is zero. The source does not specify an onset: n≥2 here is the legal-lag interpretation, not a quoted source hypothesis. Every such n is included.

Let c be the Catalan series rescaled by -1. The existing Catalan identity gives Xc²+c=1, so B=1+2Xc satisfies B²=1+4X. Its derivative companion D=(Xc)' satisfies BD=1. Expansion X↦X² constructs S=B(X²), and the two square-root branches are separated by the constant coefficient. The coefficients of D are b(m)=(-1)^m binomial(2m,m); thus a(2m)=a(2m+1)=b(m). The existing adjacent central-binomial identity gives (m+1)b(m+1)+2(2m+1)b(m)=0. Splitting n into even and odd cases and normalizing rational polynomial arithmetic yields the displayed recurrence.

Mathar's paper on P-finite recurrences includes A128057 in Example 4 and provides a general method. The bounded passage inspection recorded with the source identifies no explicit settlement of this exact shorter recurrence; global or implicit prior settlement is unmeasured. No global novelty claim is made.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MatharA128057ThreeTermRecurrence.result`
