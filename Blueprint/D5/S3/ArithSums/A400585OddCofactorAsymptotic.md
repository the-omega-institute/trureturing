# A400585: the odd-cofactor summatory asymptotic

## Abstract

The odd-cofactor binomial divisor sum has the cubic asymptotic proposed in A400585.

**Definition 1.1 (The divisor sum).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{d \in \operatorname{divisors}\left(n\right)} (\operatorname{ite}\left(\operatorname{Odd}\left(\operatorname{natDiv}\left(n, d\right)\right), \operatorname{binomial}\left(d, 2\right), 0\right))$$

*Formalization.* `D5/S3/ArithSums/A400585OddCofactorAsymptotic.a` (`✓ std3`).

*Citation.* Jishnu Babu Ranitha; Vaclav Kotesovec (2026). *A400585 — odd-cofactor binomial divisor sums and a cubic summatory conjecture*. URL: <https://oeis.org/A400585>.

*Commentary.*

a(n) = Sum_{d|n, n/d odd} binomial(d, 2). This is the NAME of OEIS A400585. In the formula, divisors(n) is the finset of positive divisors for n>0, and divisors(0) is empty. natDiv(n,d) means natural-number division, or floor(n/d); on these positive divisors it is the exact integer cofactor. ite(P,x,y) is x when P holds and y otherwise. binomial(d,2) is the natural binomial coefficient. The source offset is one.

**Definition 1.2 (The positive-prefix sum).**

$$\forall N \in \mathbb{N},\; \operatorname{S}\left(N\right) = \sum_{n \in \operatorname{Ioc}\left(0, N\right)} ((\operatorname{a}\left(n\right): \mathbb{R}))$$

*Formalization.* `D5/S3/ArithSums/A400585OddCofactorAsymptotic.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jishnu Babu Ranitha; Vaclav Kotesovec (2026). *A400585 — odd-cofactor binomial divisor sums and a cubic summatory conjecture*. URL: <https://oeis.org/A400585>.

*Commentary.*

S(N) is real-valued. Ioc(0,N) contains exactly the natural indices 1 through N. Each natural value a(n) is cast to the reals before summation; at N=0 the sum is empty.

**Definition 1.3 (The real cubic reciprocal series).**

$$\operatorname{Z3} = \sum_{q \in \mathbb{N}} (\frac{1}{((q + 1: \mathbb{N}): \mathbb{R})^{3}})$$

*Formalization.* `D5/S3/ArithSums/A400585OddCofactorAsymptotic.Z3` (`✓ std3`).

*Citation.* Jishnu Babu Ranitha; Vaclav Kotesovec (2026). *A400585 — odd-cofactor binomial divisor sums and a cubic summatory conjecture*. URL: <https://oeis.org/A400585>.

*Commentary.*

Z3 is the real series defining zeta(3). The natural index q+1 enumerates each positive denominator once. The displayed division is real division. The proof establishes summability and strict positivity of this series.

**Theorem 1.4 (The full natural ratio limit).**

$$\operatorname{Tendsto}\left(((N: \mathbb{N}) \mapsto \frac{\operatorname{S}\left(N\right)}{(\frac{7 \cdot \operatorname{Z3}}{48}) \cdot (N: \mathbb{R})^{3}}), atTop, \operatorname{nhds}\left((1: \mathbb{R})\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/A400585OddCofactorAsymptotic.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400585-odd-cofactor-asymptotic` (proved) by `D5/S3/ArithSums/A400585OddCofactorAsymptotic.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400585-odd-cofactor-asymptotic","declaration_gid":"D5/S3/ArithSums/A400585OddCofactorAsymptotic.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jishnu Babu Ranitha; Vaclav Kotesovec (2026). *A400585 — odd-cofactor binomial divisor sums and a cubic summatory conjecture*. URL: <https://oeis.org/A400585>.

*Commentary.*

Conjecture: Sum_{k=1..n} a(k) ~ 7*zeta(3)*n^3/48. - _Vaclav Kotesovec_, Oct 01 2026 This is the FORMULA conjecture of OEIS A400585, revision 22. Tendsto is convergence of the displayed real-valued function along the natural atTop filter to the real neighbourhood filter at one. All natural indices are retained, with no hypotheses. The value at zero has no effect on the limit. Reindexing by the odd cofactor q expresses S(N) as the sum of binomial(natDiv(N,q)+1,3) over odd q from one through N. The binomial equals (m^3-m)/6 for m=natDiv(N,q). Its normalized pointwise limit is 1/(6q^3), dominated by the summable cubic reciprocal series. Dominated-series convergence and the even/odd split give the constant 7*Z3/48. Its positivity permits the final ratio normalization.

## References

- Truth anchor: `D5/S3/ArithSums/A400585OddCofactorAsymptotic.S`
- Truth anchor: `D5/S3/ArithSums/A400585OddCofactorAsymptotic.Z3`
- Truth anchor: `D5/S3/ArithSums/A400585OddCofactorAsymptotic.a`
- Truth anchor: `D5/S3/ArithSums/A400585OddCofactorAsymptotic.result`
