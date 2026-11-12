# A289923: coefficientwise left limit and nonnegativity

## Abstract

The coefficientwise left limit defining OEIS A289923 exists uniquely and is nonnegative at every index.

Clark Kimberling's OEIS A289923 defines the limiting sequence from the left at the rational parameter 19/21 and conjectures that all terms are nonnegative. Every index below ranges over the natural numbers, including zero. The parameter is real; coefficients and sequence values are integers. Each coefficient may have its own positive neighborhood. No single fixed approximation to the parameter is used.

**Definition 1.1 (The real-parameter denominator).**

$$\forall r: \mathbb{R}, \forall k: \mathbb{N}, \operatorname{coeff}\left(k, \operatorname{parameterDenominator}\left(r\right)\right) = (0-1)^{k} \cdot \operatorname{floor}\left(1 + \left(k + 1\right) \cdot r\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.parameterDenominator` (`✓ std3`).

*Citation.* Clark Kimberling; Colin Barker (2017). *OEIS A289923: limiting inverse coefficients at 19/21 from the left*. URL: <https://oeis.org/A289923>.

*Commentary.*

The coefficient at index k is the signed floor from the source definition. For parameters strictly between zero and one, its constant coefficient is one.

**Definition 1.2 (The normalized formal inverse).**

$$\forall r: \mathbb{R}, \operatorname{parameterInverse}\left(r\right) = \operatorname{invOfUnit}\left(\operatorname{parameterDenominator}\left(r\right), 1\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.parameterInverse` (`✓ std3`).

*Citation.* Clark Kimberling; Colin Barker (2017). *OEIS A289923: limiting inverse coefficients at 19/21 from the left*. URL: <https://oeis.org/A289923>.

*Commentary.*

The unit inverse is invOfUnit with the unit one. On the stated parameter domain, its product with the denominator is one.

**Definition 1.3 (The coefficientwise left-limit property).**

$$\forall a: \mathbb{N} \to \mathbb{Z}, \operatorname{IsLeftLimit}\left(a\right) \iff \forall n: \mathbb{N}, \exists delta: \mathbb{R}, (0 < delta) \land (\forall r: \mathbb{R}, ((0 < r) \land (r < 1) \land (\frac{19}{21} - delta < r) \land (r < \frac{19}{21})) \implies (\operatorname{coeff}\left(n, \operatorname{parameterInverse}\left(r\right)\right) = a\left(n\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.IsLeftLimit` (`✓ std3`).

*Citation.* Clark Kimberling; Colin Barker (2017). *OEIS A289923: limiting inverse coefficients at 19/21 from the left*. URL: <https://oeis.org/A289923>.

*Commentary.*

At each index n there is a positive delta such that every real parameter in the specified left interval, also strictly between zero and one, has the same inverse coefficient. Delta may depend on n.

For indices at most n, delta equal to the reciprocal of 21 times n+1 stabilizes every floor coefficient. The existing AbsoluteReciprocalGeometricParity.agree_inv theorem transports this finite coefficient agreement through the normalized inverse. Two candidate limit sequences agree by choosing a parameter in the intersection of their two positive left neighborhoods.

Write D for the series with coefficient (-1) to the k times the natural quotient (19(k+1)+20)/21. The quotient shifts by 19 after 21 steps. Consequently the coefficients of D times (1+X) squared change sign after 21 steps beyond the initial two coefficients. This proves the full series identity D P = Q, where P=(1+X)^2(1+X^21) and Q=1-X^10-X^11-X^20. Multiplying by the unit inverse gives Q F=P. Its coefficient recurrence expresses each coefficient of F as the nonnegative coefficient of P plus coefficients at the strictly smaller indices n-10, n-11 and n-20 when those indices exist. Strong induction proves nonnegativity. The finite initial coefficient cases certify a symbolic identity with an all-degree shift proof; they do not replace the universal theorem. Colin Barker's rational generating function is a known source formula, and is not assumed as the connection to the limiting sequence.

**Theorem 1.4 (The complete left-limit theorem).**

$$\exists a: \mathbb{N} \to \mathbb{Z}, (\operatorname{IsLeftLimit}\left(a\right)) \land (\forall b: \mathbb{N} \to \mathbb{Z}, (\operatorname{IsLeftLimit}\left(b\right)) \implies (b = a)) \land (\forall n: \mathbb{N}, 0 \le a\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Clark Kimberling; Colin Barker (2017). *OEIS A289923: limiting inverse coefficients at 19/21 from the left*. URL: <https://oeis.org/A289923>.

*Commentary.*

There is a limit sequence, every other sequence satisfying the same left-limit property equals it, and every one of its terms is nonnegative.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.IsLeftLimit`
- Truth anchor: `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.parameterDenominator`
- Truth anchor: `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.parameterInverse`
- Truth anchor: `D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative.result`
- Dependency: [D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity](AbsoluteReciprocalGeometricParity.md)
