# White to Haar Identity

## Abstract

Resolvent-weighted Cayley compactification carries normalized white spectrum to normalized circle Haar spectrum with the exact scale factor.

**Definition 1.1 (Normalized Lebesgue spectrum).**

$$m_{0}: \operatorname{Measure}(\mathbb{R}) = \operatorname{ofReal}(\frac{1}{2 \cdot \pi}) \cdot \operatorname{volume}(\mathbb{R}).$$

*Formalization.* `D5/S3/Weil/Budget/WhiteToHaarIdentity.normalizedLebesgueSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source white spectrum is constructed as Lebesgue measure on the real line scaled by the reciprocal of two pi.

**Definition 1.2 (Cayley map into the unit circle).**

$$\forall a: \mathbb{R}, h: a \neq 0, xi: \mathbb{R},\\{}\operatorname{cayleyCircle}(a, h, xi) = \operatorname{ofConjDivSelf}((xi: \operatorname{Complex}()) - i \cdot a): Circle.$$

*Formalization.* `D5/S3/Weil/Budget/WhiteToHaarIdentity.cayleyCircle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map is the canonical conjugate-over-self circle point. Its nonzero scale premise ensures that the denominator never vanishes.

**Definition 1.3 (Resolvent compactification).**

$$\forall a: \mathbb{R}, h: a \neq 0, \nu: \operatorname{Measure}(\mathbb{R}),\\{}\operatorname{resolventCompactification}(a, h, \nu) = \operatorname{map}(\operatorname{cayleyCircle}(a, h), \operatorname{withDensity}(\nu, \operatorname{lambda}(xi: \mathbb{R}, \operatorname{ofReal}(\frac{1}{\operatorname{sq}(xi) + \operatorname{sq}(a)})))).$$

*Formalization.* `D5/S3/Weil/Budget/WhiteToHaarIdentity.resolventCompactification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compactification first weights the source measure by the reciprocal quadratic resolvent and then pushes it through the Cayley map.

**Theorem 1.4 (White spectrum becomes Haar spectrum).**

$$\forall a: \mathbb{R}, lambda: ENNReal, \nu: \operatorname{Measure}(\mathbb{R}),\\{}0 < a \Rightarrow\\{}(\operatorname{resolventCompactification}(a, m_{0}) = \operatorname{ofReal}(\frac{1}{2 \cdot a}) \cdot m_{T}) \land\\{}(\operatorname{resolventCompactification}(a, lambda \cdot m_{0}) = (lambda \cdot \operatorname{ofReal}(\frac{1}{2 \cdot a})) \cdot m_{T}) \land\\{}((lambda \cdot m_{0} \leq \nu) \Leftrightarrow ((lambda \cdot \operatorname{ofReal}(\frac{1}{2 \cdot a})) \cdot m_{T} \leq \operatorname{resolventCompactification}(a, \nu))) \land\\{}(\operatorname{resolventCompactification}(\frac{1}{2}, lambda \cdot m_{0}) = lambda \cdot m_{T}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/WhiteToHaarIdentity.white_to_haar_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All binders and the positive-scale premise are displayed. The first two clauses give the base and arbitrary-intensity identities.

The third clause reflects measure domination in both directions, so the real-line white floor and circle Haar floor are equivalent.

At scale one half the coefficient is exactly one, giving the final scale-free correspondence.

## References

- Truth anchor: `D5/S3/Weil/Budget/WhiteToHaarIdentity.cayleyCircle`
- Truth anchor: `D5/S3/Weil/Budget/WhiteToHaarIdentity.normalizedLebesgueSpectrum`
- Truth anchor: `D5/S3/Weil/Budget/WhiteToHaarIdentity.resolventCompactification`
- Truth anchor: `D5/S3/Weil/Budget/WhiteToHaarIdentity.white_to_haar_identity`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](FullCirclePrimalAttainment.md)
- Dependency: [D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography](../TestFunctions/CayleyLaguerreMomentTomography.md)
