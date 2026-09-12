# Hermite upper envelope

## Abstract

A positive third derivative makes the Hermite quadratic an upper bound, and matching two moments evaluates its sum.

**Theorem 1.1 (Remainder on an open domain).**

$$\exists z \in (L,H): \operatorname{f}\left(x\right)-\operatorname{p}\left(x\right) = \frac{\operatorname{iteratedDeriv}\left(3, f, z\right)}{6}(x-L)^{2}(x-H) \land \operatorname{f}\left(x\right)-\operatorname{p}\left(x\right) < 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_two_point_remainder_on` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be an open subset of the real line containing the closed interval from L to H, and let x lie strictly between L and H. Assume f and p are three times continuously differentiable on s, the third derivative of p is zero on s, p and f agree in value and first derivative at L, and they agree in value at H. If the third derivative of f is positive between the nodes, there is a point z strictly between them with the following remainder and strict sign. Replacing f-p by a globally smooth function agreeing near the closed interval permits the usual Hermite remainder formula to apply.

**Theorem 1.2 (An upper bound determined by the mean and variance).**

$$\forall k: \operatorname{Nat}\left(\right), \forall x: \operatorname{Fin}\left(k\right) \to \operatorname{Real}\left(\right), (2 \le k \land (\forall i: \operatorname{Fin}\left(k\right), 0 < \operatorname{x}\left(i\right))) \implies \sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(\operatorname{x}\left(i\right)\right) \le \operatorname{f}\left(H\right)+(k-1)\operatorname{f}\left(L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_upper_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a natural number at least two and let every coordinate x indexed by Fin k be a positive real number. Let m be the arithmetic mean and V the total squared deviation, without division by k. Define the radius r and nodes L and H as follows.

$m = \frac{\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{x}\left(i\right)}{k}, V = \sum_{i \in \operatorname{Fin}\left(k\right)} (\operatorname{x}\left(i\right)-m)^{2}, r = \sqrt{\frac{V}{k(k-1)}}, L = m-r, H = m+(k-1)r$

$f(t) = \log(1-\exp(-t))$

The moment bounds give a positive L and place every coordinate at or below H. If V is zero, all coordinates equal m and both sides coincide. Otherwise L is strictly below H. Take the quadratic p agreeing with f in value and first derivative at L and in value at H.

For a coordinate between the nodes the remainder formula gives f less than p. For a positive coordinate to the left of L, suppose f minus p were nonnegative. Two applications of the mean value theorem then give a nonnegative second derivative to the left of L, while two applications of Rolle's theorem give a zero second derivative to its right. This contradicts strict increase of the second derivative. At either node the values agree.

Writing the quadratic in powers of t-L reduces its sum to the first and second displacement moments. These equal kr and k squared times r squared, respectively, since V equals k(k-1) times r squared. Thus the quadratic sum equals p(H)+(k-1)p(L), which gives the stated bound after substitution.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_two_point_remainder_on`
- Truth anchor: `D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_upper_envelope`
- Dependency: [D5/S3/Analytic/Interpolation/HermiteMomentBounds](HermiteMomentBounds.md)
- Dependency: [D5/S3/Analytic/Interpolation/HermiteTwoPointRemainder](HermiteTwoPointRemainder.md)
- Dependency: [D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives](LogOneSubExpDerivatives.md)
