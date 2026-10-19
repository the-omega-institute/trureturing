# Hanna's dyadic vanishing conjecture for A271960

## Abstract

Reversion and dyadic coefficient decimation prove Hanna's A271960 conjecture.

All series have rational coefficients. The operation subst(u,f) is PowerSeries.subst u f, namely f(u). Natural subtraction in the coefficient index is exact under the displayed bounds.

**Definition 1.1 (The normalized generating function).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right) \iff ((\operatorname{constantCoeff}\left(A\right) = 0) \land ((\operatorname{coeff}\left(1, A\right) = 1) \land ((A)^{2} = \operatorname{subst}\left((X + 2 \cdot (A)^{2})^{2}, A\right)))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.IsGF` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A271960: a squared compositional generating function and dyadic vanishing*. URL: <https://oeis.org/A271960>.

*Commentary.*

OEIS A271960, NAME (unpaginated): "G.f. A(x) satisfies: A(x)^2 = A( (x + 2*A(x)^2)^2 )." OFFSET 1 and EXAMPLE A(x) = x + 2*x^2 + 9*x^3 + 50*x^4 + 312*x^5 + … specify zero constant coefficient and linear coefficient one.

**Definition 1.2 (The quotient x divided by A(x)).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{xOverA}\left(A\right) = (\operatorname{mk}\left((n: \mathbb{N} \mapsto \operatorname{coeff}\left(n + 1, A\right))\right))^{-1})$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.xOverA` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271960: a squared compositional generating function and dyadic vanishing*. URL: <https://oeis.org/A271960>.

*Commentary.*

Deleting the zero constant coefficient from A gives A(x)/x. Its multiplicative inverse is x/A(x); the linear coefficient of A makes this series a unit.

**Definition 1.3 (The OEIS conjecture).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (\forall k: \mathbb{N}, ((2 \leq n) \implies ((k \leq n - 2) \implies (\operatorname{coeff}\left((2)^{n} - (2)^{k}, (\operatorname{xOverA}\left(A\right))^{(2)^{n}}\right) = 0))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2016). *OEIS A271960: a squared compositional generating function and dyadic vanishing*. URL: <https://oeis.org/A271960>.

*Commentary.*

OEIS A271960, COMMENTS (unpaginated): "Conjecture: [x^(2^n-2^k)] (x/A(x))^(2^n) = 0 for k = 0..n-2 and n >= 2. - _Paul D. Hanna_, Jan 16 2026" Here n and k are natural numbers, coeff extracts a coefficient, and IsGF also specifies the normalization. The proposition includes existence of a solution and the assertion for every normalized solution.

**Theorem 1.4 (Dyadic vanishing).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (\forall k: \mathbb{N}, ((2 \leq n) \implies ((k \leq n - 2) \implies (\operatorname{coeff}\left((2)^{n} - (2)^{k}, (\operatorname{xOverA}\left(A\right))^{(2)^{n}}\right) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a271960-dyadic-vanishing` (proved) by `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a271960-dyadic-vanishing","declaration_gid":"D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2016). *OEIS A271960: a squared compositional generating function and dyadic vanishing*. URL: <https://oeis.org/A271960>.

*Commentary.*

Let B be the compositional inverse of A and H=B+2X^2. The defining equation implies H^2=B(X^2), and the linear coefficient of H forces H(-X)=-H(X). Expanding B^r=(H-2X^2)^r eliminates odd powers at even degrees; the remaining terms reduce both degree and exponent by a factor of two. Induction proves coeff N (B^r)=0 whenever 2r<N, 2^s divides N-2r and r<2^s. Lagrange inversion transfers this to the displayed coefficient with N=2^n and r=2^k. Existence follows by coefficientwise stabilization of the iteration F ↦ F + (F(X^2)-F^2-2X)/2, starting at one, followed by compositional inversion.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.IsGF`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.result`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA271960DyadicVanishing.xOverA`
- Dependency: [D5/S1/Recurrence/Invariants/SignedCatalanCubicSubstitutionModThree](SignedCatalanCubicSubstitutionModThree.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../../../S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.md)
