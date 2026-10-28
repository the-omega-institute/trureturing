# Tebni's A341724 prime and dyadic row divisibility

## Abstract

Both original A341724 row-divisibility conjectures hold for the integral coefficients of the exact column EGF.

All indices and exponents are natural, including zero. The coefficients lie in Q, and the inverse is the formal power-series inverse. The odd Taylor series sinh is TebniA364822.sinh. Rescaling it by -1 substitutes -X, so the denominator is 1+2 sinh(X). The constant series C embeds a rational scalar. Integer witnesses equal the rational coefficients after casting to Q; the row modulus is cast to Z.

**Definition 1.1 (The original denominator).**

$$\operatorname{denominator} = 1 - (2) \cdot (\operatorname{PowerSeries}.\operatorname{rescale}\left(-1, \operatorname{TebniA364822}.\operatorname{sinh}\right))$$

*Formalization.* `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.denominator` (`✓ std3`).

*Citation.* M. Tebni (2023). *OEIS A341724, Column EGF and prime and dyadic row-divisibility conjectures*. URL: <https://oeis.org/A341724>.

*Commentary.*

OEIS A341724 specifies the column denominator as 1-2 sinh(-X). Oddness of the Taylor series gives 1+2 sinh(X); in particular its constant coefficient is one.

**Definition 1.2 (The literal column EGF).**

$$\forall k: \mathbb{N}, \operatorname{column}\left(k\right) = (X^{k}) \cdot ((\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{factorial}\left(k\right): \mathbb{Q}))^{-1}\right)) \cdot ((1 - (2) \cdot (\operatorname{PowerSeries}.\operatorname{rescale}\left(-1, \operatorname{TebniA364822}.\operatorname{sinh}\right)))^{-1}))$$

*Formalization.* `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.column` (`✓ std3`).

*Citation.* M. Tebni (2023). *OEIS A341724, Column EGF and prime and dyadic row-divisibility conjectures*. URL: <https://oeis.org/A341724>.

*Commentary.*

The displayed product is X^k divided by the product of k! and the original denominator. The scalar inverse and the formal inverse are taken in their respective carriers.

**Definition 1.3 (Factorial-normalized column coefficients).**

$$\forall n: \mathbb{N}, \forall k: \mathbb{N}, \operatorname{Tq}\left(n, k\right) = ((\operatorname{Nat}.\operatorname{factorial}\left(n\right): \mathbb{Q})) \cdot (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, (X^{k}) \cdot ((\operatorname{PowerSeries}.\operatorname{C}\left(((\operatorname{Nat}.\operatorname{factorial}\left(k\right): \mathbb{Q}))^{-1}\right)) \cdot ((1 - (2) \cdot (\operatorname{PowerSeries}.\operatorname{rescale}\left(-1, \operatorname{TebniA364822}.\operatorname{sinh}\right)))^{-1}))\right))$$

*Formalization.* `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.Tq` (`✓ std3`).

*Citation.* M. Tebni (2023). *OEIS A341724, Column EGF and prime and dyadic row-divisibility conjectures*. URL: <https://oeis.org/A341724>.

*Commentary.*

The source array is n! times the nth ordinary coefficient of its kth column. A column has no terms below degree k and has factorial-normalized diagonal coefficient one.

**Definition 1.4 (Both conjectures with their complete domains).**

$$\operatorname{claim} \iff ((\forall p: \mathbb{N}, \forall k: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((0 < k) \implies ((k < p) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{Tq}\left(p, k\right)) \land ((p: \mathbb{Z}) \mid z))))) \land (\forall m: \mathbb{N}, \forall k: \mathbb{N}, (k < 2^{m}) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{Tq}\left(2^{m}, k\right)) \land ((2^{m}: \mathbb{Z}) \mid z))))$$

*Formalization.* `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.claim` (`✓ std3`).

*Citation.* M. Tebni (2023). *OEIS A341724, Column EGF and prime and dyadic row-divisibility conjectures*. URL: <https://oeis.org/A341724>.

*Commentary.*

M. Tebni's OEIS conjectures require 0<k<p at a prime row and 0<=k<2^m at a dyadic row. The prime two is included. The dyadic clause includes k=0 and m=0, when the modulus is one. Each clause asserts integrality as well as divisibility.

**Theorem 1.5 (Prime and dyadic row divisibility).**

$$(\forall p: \mathbb{N}, \forall k: \mathbb{N}, (\operatorname{Nat}.\operatorname{Prime}\left(p\right)) \implies ((0 < k) \implies ((k < p) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{Tq}\left(p, k\right)) \land ((p: \mathbb{Z}) \mid z))))) \land (\forall m: \mathbb{N}, \forall k: \mathbb{N}, (k < 2^{m}) \implies (\exists z: \mathbb{Z}, ((z: \mathbb{Q}) = \operatorname{Tq}\left(2^{m}, k\right)) \land ((2^{m}: \mathbb{Z}) \mid z)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.result` (`✓ std3`). ∎

*Resolves.* `Problems/tebni341724-row-divisibility` (proved) by `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tebni341724-row-divisibility","declaration_gid":"D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. Tebni (2023). *OEIS A341724, Column EGF and prime and dyadic row-divisibility conjectures*. URL: <https://oeis.org/A341724>.

*Commentary.*

Multiplying the exact column by 1+2 sinh(X) gives X^k/k!. The factorial-normalized product formula yields the forcing term equal to one precisely when n=k, minus twice the sum of choose(n,j) Tq(n-j,k) over positive odd j<=n. Strong induction gives integral coefficients, using support below the diagonal and the diagonal value one. For n>k the forcing vanishes. At a prime p every interior binomial term is divisible by p; the j=p endpoint is zero because k>0 implies Tq(0,k)=0. At a dyadic row every odd-index binomial coefficient is divisible by the row index. These arguments retain the prime two and exponent zero.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.Tq`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.column`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.denominator`
- Truth anchor: `D5/S1/Recurrence/Residue/TebniA341724RowDivisibility.result`
- Dependency: [D5/S1/Recurrence/Residue/IntegralEGFComposition](IntegralEGFComposition.md)
- Dependency: [D5/S1/Recurrence/Residue/TebniA364822](TebniA364822.md)
- Dependency: [D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo](TebniA364822PowerOfTwo.md)
