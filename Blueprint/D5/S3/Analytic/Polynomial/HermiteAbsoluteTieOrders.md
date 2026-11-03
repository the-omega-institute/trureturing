# Orders with two maximal absolute Hermite coefficients

## Abstract

The exact increasing enumeration of physicists Hermite orders with exactly two largest absolute coefficients.

The order k and every exponent are natural numbers, including zero. The polynomial is exactly HermiteSignedMode.physicistsHermite over the rationals. Maximality compares absolute values over the entire coefficient row from zero through k, including the zero coefficients of the other parity. The index n of the enumeration starts at one. Its formula uses integer arithmetic, so the alternating summand is an ordinary signed integer.

**Definition 1.1 (Maximality in the complete original row).**

$$\forall k:\mathbb{N}, \forall j:\mathbb{N}, \operatorname{IsAbsMax}\left(k, j\right) = ((j \le k) \land (\forall i:\mathbb{N}, (i \le k) \implies (\operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(k\right), i\right)\right) \le \operatorname{abs}\left(\operatorname{coeff}\left(\operatorname{physicistsHermite}\left(k\right), j\right)\right))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.IsAbsMax` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

An exponent j is at most k and its absolute coefficient bounds the absolute coefficient at every exponent i at most k.

**Definition 1.2 (Exactly two distinct maxima).**

$$\forall k:\mathbb{N}, \operatorname{HasExactlyTwo}\left(k\right) = (\exists u:\mathbb{N}, \exists v:\mathbb{N}, (u < v) \land (\forall j:\mathbb{N}, (\operatorname{IsAbsMax}\left(k, j\right)) \iff ((j = u) \lor (j = v))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.HasExactlyTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

There are exponents u less than v such that the maximizing exponents are precisely u and v. The equivalence for every natural j excludes both additional maxima and exponents outside the row.

**Definition 1.3 (The one-based source formula).**

$$\forall n:\mathbb{N}, \operatorname{a}\left(n\right) = ((2) \cdot ((n:\mathbb{Z}))) \cdot (((n:\mathbb{Z})+2))+(((n:\mathbb{Z})+1)) \cdot ((-1)^{n+1})$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.a` (`✓ std3`).

*Citation.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

This is Conjecture 1 of OEIS A381737 revision 28. The natural index is cast to the integers before the additions and products. The exponent n+1 remains natural. The theorem uses only positive indices.

**Definition 1.4 (The complete increasing exhaustive enumeration).**

$$claim = ((\forall n:\mathbb{N}, (1 \le n) \implies (0 < \operatorname{a}\left(n\right))) \land ((\forall n:\mathbb{N}, \forall m:\mathbb{N}, (1 \le n) \implies ((n < m) \implies (\operatorname{a}\left(n\right) < \operatorname{a}\left(m\right)))) \land (\forall k:\mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n:\mathbb{N}, ((1 \le n) \land ((k:\mathbb{Z}) = \operatorname{a}\left(n\right))) \land (\forall m:\mathbb{N}, ((1 \le m) \land ((k:\mathbb{Z}) = \operatorname{a}\left(m\right))) \implies (m = n))))))$$

*Formalization.* `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

Every positive-index value is positive; the values strictly increase with the index; and for every natural order k, exactly two maxima occur if and only if k equals the formula at one unique positive index. The displayed unique-index condition expands existence and uniqueness explicitly.

**Theorem 1.5 (Exact classification and enumeration).**

$$(\forall n:\mathbb{N}, (1 \le n) \implies (0 < \operatorname{a}\left(n\right))) \land ((\forall n:\mathbb{N}, \forall m:\mathbb{N}, (1 \le n) \implies ((n < m) \implies (\operatorname{a}\left(n\right) < \operatorname{a}\left(m\right)))) \land (\forall k:\mathbb{N}, (\operatorname{HasExactlyTwo}\left(k\right)) \iff (\exists n:\mathbb{N}, ((1 \le n) \land ((k:\mathbb{Z}) = \operatorname{a}\left(n\right))) \land (\forall m:\mathbb{N}, ((1 \le m) \land ((k:\mathbb{Z}) = \operatorname{a}\left(m\right))) \implies (m = n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a381737-hermite-absolute-ties` (proved) by `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a381737-hermite-absolute-ties","declaration_gid":"D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Sheppard (2025). *Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice*. URL: <https://oeis.org/A381737/internal?rev=28>.

*Commentary.*

Let w(k,r) be the original absolute signedCoeff at exponent k-2r, with 2r at most k. HermiteAbsoluteMode supplies positivity, the adjacent identity, maximality at mode(k), and strict decrease after that mode. Before the final adjacent pair, the threshold is strict: if r+1 is less than mode(k), then 4(r+1) is less than second(k-2(r+1)), where second(j)=(j+1)(j+2). The adjacent identity therefore gives w(k,r) less than w(k,r+1). A maximizing index must be mode(k) or mode(k)-1. Those two indices tie exactly when second(k-2r)=4r at r=mode(k), with r at least one. Conversely, any such equality forces r to be mode(k) and gives precisely those two maxima. The coefficient_cases and polynomial_coeff statements transfer the comparison to every exponent in the original polynomial row; zero parity coefficients cannot maximize because the mode weight is positive.

Put j=k-2r. The tie equation is (j+1)(j+2)=4r. Its reduction modulo four forces j to be 4t+2 or 4t+3. In the first case k=8t squared+18t+8=a(2t+1); in the second, k=8t squared+22t+13=a(2t+2). Conversely, these formulas provide r=(4t+3)(t+1) and r=(4t+5)(t+1), respectively, satisfying the tie equation and 2r at most k. Every positive index is uniquely odd or even in these forms. The alternating power is either one or minus one; substitution shows that a(n+1)-a(n) is 2n+3 or 6n+9, both positive. Thus the enumeration is strictly increasing, and a(1)=8 makes every positive-index value positive. Strict increase gives the unique positive index for each qualifying order. No finite cutoff, rescaling of the coefficient row, or restriction to a subsequence is used.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.HasExactlyTwo`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.IsAbsMax`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.a`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.claim`
- Truth anchor: `D5/S3/Analytic/Polynomial/HermiteAbsoluteTieOrders.result`
- Dependency: [D5/S3/Analytic/Polynomial/HermiteAbsoluteMode](HermiteAbsoluteMode.md)
