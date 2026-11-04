# A391810: alternating Laurent rows and Jacobsthal numbers

## Abstract

For every positive row, the signed alternating sum of the original bilateral Laurent coefficients is twice round(2^n/3), and hence twice the offset-zero Jacobsthal number.

**Definition 1.1 (The offset-zero Jacobsthal recurrence).**

$$\operatorname{jacobsthal}\left(0\right) = 0 \land \left(\operatorname{jacobsthal}\left(1\right) = 1 \land \left(\forall n \in \mathbb{N},\; \operatorname{jacobsthal}\left(n + 2\right) = \operatorname{jacobsthal}\left(n + 1\right) + 2 \cdot \operatorname{jacobsthal}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.jacobsthal` (`✓ std3`).

*Citation.* The OEIS Foundation Inc. (2026). *OEIS A001045: Jacobsthal numbers, revision 1350*. URL: <https://oeis.org/A001045/internal>.

*Commentary.*

This is A001045 with index zero included, valued in the integers. Two-step induction gives 3 J(n)=2^n-(-1)^n. Its parity term is always 1 or -1, placing 2^n/3 in the nearest-integer interval [J(n)-1/2,J(n)+1/2). The root-namespace round operation uses ties toward positive infinity. These familiar Jacobsthal identities supply the arithmetic interpretation, without a separate novelty claim.

**Theorem 1.2 (The full alternating, rounding and Jacobsthal formula).**

$$\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\sum_{0 \leq k < \left\lfloor\frac{n + 1}{2}\right\rfloor^{2} + 1} -(-1)^{k} \cdot \operatorname{rowEntry}\left(n, k\right) = 2 \cdot \operatorname{round}\left(\frac{2^{n}}{3}\right) \land \left(2 \cdot \operatorname{round}\left(\frac{2^{n}}{3}\right) = 2 \cdot \operatorname{jacobsthal}\left(n\right) \land \left(\sum_{0 \leq k < \left\lfloor\frac{n + 1}{2}\right\rfloor^{2} + 1} -(-1)^{k} \cdot \operatorname{coeff}\left(\operatorname{series}\left(n\right), -k\right) = 2 \cdot \operatorname{round}\left(\frac{2^{n}}{3}\right) \land \left(\left(\forall k \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{series}\left(n\right), -k\right) = \operatorname{rationalCast}\left(\operatorname{rowEntry}\left(n, k\right)\right)\right) \land \left(\forall k \in \mathbb{N},\; \left\lfloor\frac{n + 1}{2}\right\rfloor^{2} < k \Rightarrow \operatorname{coeff}\left(\operatorname{series}\left(n\right), -k\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.full_formula_five` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a391810-alternating-jacobsthal` (proved) by `D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.full_formula_five`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a391810-alternating-jacobsthal","declaration_gid":"D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.full_formula_five","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A391810, nonpositive Laurent coefficients and zero row sums*. URL: <https://oeis.org/A391810/internal>.

*Commentary.*

The imported HannaLaurentRowSums series is the formal expansion at zero of the sum over every integer outer index j of x^j(1-x^j)^(n+j). Negative integer powers use Laurent-field inverses. Its coefficient at -k is the rational cast of the signed integer rowEntry(n,k). Natural-number division gives the published floor bound; the finite range includes k=0 and the upper endpoint.

Write P_n(y)=-1+sum from j=1 to n of y^j(1-y^j)^(n-j), with y the inverse Laurent variable. Only this finite polynomial is evaluated at -1. Shifting its finite index by two proves P_(n+2)(-1)=P_n(-1)-2^(n+1) for n>0. A positive-index two-step induction, with rows one and two checked separately, combines this identity with J(n+2)=J(n)+2^n to obtain P_n(-1)=-2 J(n). The imported degree bound and polynomial coefficient evaluation identify the negative of this value with the complete alternating coefficient sum.

The displayed five clauses retain both equalities of formula (5), the rational original-series equality, the coefficient identification for every natural k, and vanishing past the inclusive bound. Casting the integer round/Jacobsthal equality yields the rational-series/Jacobsthal equality as well. Neither the bilateral series nor its summands are evaluated at 1 or -1. At n=0 the finite polynomial has value -1, whereas J(0)=0; the alternating-row theorem therefore retains precisely the source range n>=1. No global literature-priority or other A391810 conjecture is asserted.

## References

- Truth anchor: `D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.full_formula_five`
- Truth anchor: `D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.jacobsthal`
- Dependency: [D5/S3/ArithSums/HannaLaurentRowSums](HannaLaurentRowSums.md)
