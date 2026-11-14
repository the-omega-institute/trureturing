# Mathar's recurrence for the literal A117187 generating function

## Abstract

The literal Catalan generating function in A117187 satisfies the printed order-three recurrence at every nonnegative-index onset.

All series are formal power series over the integers; no analytic convergence is assumed. C is the standard Catalan series, Cprime is its formal derivative, and T(f) substitutes X squared for X. Thus T(f)=f(X²). The map U selects the inverse of a series whose constant coefficient is the unit 1. All sequence indices are natural numbers, while recurrence coefficients and values are integers.

**Definition 1.1 (Catalan substitution).**

$$B = \operatorname{T}\left(C\right)$$

*Formalization.* `D5/S3/Constants/Moments/A117187MatharRecurrence.catalan_square` (`✓ std3`).

*Citation.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

B=C(X²), using the standard Catalan series, rather than a sequence defined by a recurrence.

**Definition 1.2 (The normalized square-root branch).**

$$S = 1 - 2 \cdot X^{2} \cdot B$$

*Formalization.* `D5/S3/Constants/Moments/A117187MatharRecurrence.source_root` (`✓ std3`).

*Citation.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

S=1-2X²C(X²). The result proves S²=1-4X² and constant coefficient 1, and proves uniqueness among all series with these two properties.

**Definition 1.3 (The full source denominator).**

$$D = (1 - X^{2} \cdot B) \cdot S$$

*Formalization.* `D5/S3/Constants/Moments/A117187MatharRecurrence.denominator` (`✓ std3`).

*Citation.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

D is exactly (1-X²C(X²))sqrt(1-4X²) with the constant-one branch. Its constant coefficient is 1, so it has a genuine two-sided unit inverse.

**Definition 1.4 (The literal source generating function).**

$$F = (1 + X) \cdot B \cdot \operatorname{U}\left(D\right)$$

*Formalization.* `D5/S3/Constants/Moments/A117187MatharRecurrence.source_series` (`✓ std3`).

*Citation.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

F=(1+X)C(X²)/((1-X²C(X²))sqrt(1-4X²)). Division denotes multiplication by the proven unit inverse, not a formal symbol with an assumed cancellation law.

**Definition 1.5 (Offset-zero source coefficients).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \operatorname{coeff}\left(F, n\right)$$

*Formalization.* `D5/S3/Constants/Moments/A117187MatharRecurrence.a` (`✓ std3`).

*Citation.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

a(n) is the coefficient of X to the n in the complete source series F.

**Theorem 1.6 (Normalized source interpretation and the exact recurrence).**

$$(\operatorname{constantCoeff}\left(S\right) = 1 \land \left(S^{2} = 1 - 4 \cdot X^{2} \land \left(\forall r \in \operatorname{PowerSeries}\left(\mathbb{Z}\right),\; \operatorname{constantCoeff}\left(r\right) = 1 \Rightarrow \left(r^{2} = 1 - 4 \cdot X^{2} \Rightarrow r = S\right)\right)\right)) \land \left((\operatorname{IsUnit}\left(D\right) \land \left(D \cdot \operatorname{U}\left(D\right) = 1 \land \operatorname{U}\left(D\right) \cdot D = 1\right)) \land \left((F = (1 + X) \cdot \operatorname{T}\left(Cprime\right)) \land \left(\forall n \in \mathbb{N},\; 3 \le n \Rightarrow (n + 4) \cdot (31 \cdot n - 12) \cdot \operatorname{a}\left(n\right) + (37 \cdot n^{2} + 24 \cdot n - 156) \cdot \operatorname{a}\left(n - 1\right) - 4 \cdot (31 \cdot n^{2} + 81 \cdot n + 24) \cdot \operatorname{a}\left(n - 2\right) - 4 \cdot (37 \cdot n + 24) \cdot (n - 1) \cdot \operatorname{a}\left(n - 3\right) = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Moments/A117187MatharRecurrence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Barry and R. J. Mathar (2011). *OEIS A117187: Catalan generating function and conjectural recurrence*. URL: <https://oeis.org/A117187/internal>.

*Commentary.*

The Catalan quadratic identity determines the normalized square root and shows that the denominator has constant coefficient 1. The existing Catalan differential identity X(1-4X)Cprime+(1-2X)C=1, together with the quadratic equation, gives Cprime(1-2XC)=C² and C²(1-XC)=C. Substitution X to X² and cancellation with the unit inverse give the full identity F=(1+X)Cprime(X²). Consequently a(2m)=a(2m+1)=binomial(2m+2,m), reusing the Catalan derivative coefficient identity. This closed formula is already present in LODA and is used as prior mathematics here.

Write b(m)=binomial(2m+2,m). Adjacent-binomial identities give E(m)=m(m+2)b(m)-2(m+1)(2m+1)b(m-1)=0 for m≥1. For the printed residual R, polynomial normalization gives R(2m+1)=272E(m) for m≥1 and mR(2m)=4(31m-6)E(m)+4(37m+12)E(m-1) for m≥2. These two domains include every n≥3, including n=3. The source gives no explicit recurrence onset; n≥3 is exactly its order-three nonnegative-index domain. The conclusion concerns this literal source and printed recurrence; no priority assertion follows.

## References

- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.a`
- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.catalan_square`
- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.denominator`
- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.result`
- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.source_root`
- Truth anchor: `D5/S3/Constants/Moments/A117187MatharRecurrence.source_series`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../../../S1/Recurrence/A308815DFiniteRecurrence.md)
- Dependency: [D5/S3/Constants/Moments/A331474HankelBridge](A331474HankelBridge.md)
