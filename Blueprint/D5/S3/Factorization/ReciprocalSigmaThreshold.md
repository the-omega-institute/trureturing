# Reciprocal Sigma Threshold Minima

## Abstract

Reciprocal sigma sums and the first crossing of every positive integer threshold.

**Definition 1.1 (Exact divisor sum).**

$$\forall k:\mathbb{N}, \operatorname{g}(k) = \sum_{d \in \operatorname{divisors}(k)} \frac{1}{(\sigma_1(d):\mathbb{Q})}$$

*Formalization.* `D5/S3/Factorization/ReciprocalSigmaThreshold.g` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek; Robert Israel (2015). *OEIS A265714, minima of reciprocal-sigma divisor sums*. URL: <https://oeis.org/history/view?seq=A265714&v=23>.

*Commentary.*

For every natural k, g(k) is the exact rational sum over k.divisors. For positive k these are all its positive divisors. ArithmeticFunction.sigma 1 d is the natural sum of all positive divisors of d, cast to the rationals before division. The empty divisor set gives g(0)=0; the two sets below require positive integers.

**Definition 1.2 (The two positive sets).**

$$claim \iff \forall r:\mathbb{N}, 0<r \implies \exists m:\mathbb{N}, \operatorname{IsLeast}(\{k:\mathbb{N} \mid 0<k \land \lfloor \operatorname{g}(k)\rfloor = (r:\mathbb{Z})\},m) \land \operatorname{IsLeast}(\{k:\mathbb{N} \mid 0<k \land (r:\mathbb{Q}) \le \operatorname{g}(k)\},m)$$

*Formalization.* `D5/S3/Factorization/ReciprocalSigmaThreshold.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek; Robert Israel (2015). *OEIS A265714, minima of reciprocal-sigma divisor sums*. URL: <https://oeis.org/history/view?seq=A265714&v=23>.

*Commentary.*

This proposition expresses the common-minimum conjecture in OEIS A265714 revision 23. IsLeast(S,m) means that m belongs to S and is at most every member of S. The one witness m therefore makes both sets nonempty and is their common least element. Int.floor is the ordinary floor of the exact rational g(k). Its value is compared with the integer cast of r, whereas the threshold uses the rational cast. Both r and k are unbounded, and r=1 is included.

**Theorem 1.3 (A common least element).**

$$\forall r:\mathbb{N}, 0<r \implies \exists m:\mathbb{N}, \operatorname{IsLeast}(\{k:\mathbb{N} \mid 0<k \land \lfloor \operatorname{g}(k)\rfloor = (r:\mathbb{Z})\},m) \land \operatorname{IsLeast}(\{k:\mathbb{N} \mid 0<k \land (r:\mathbb{Q}) \le \operatorname{g}(k)\},m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/ReciprocalSigmaThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a265714-positive-threshold-common-minimum` (proved) by `D5/S3/Factorization/ReciprocalSigmaThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a265714-positive-threshold-common-minimum","declaration_gid":"D5/S3/Factorization/ReciprocalSigmaThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jaroslav Krizek; Robert Israel (2015). *OEIS A265714, minima of reciprocal-sigma divisor sums*. URL: <https://oeis.org/history/view?seq=A265714&v=23>.

*Commentary.*

Prime divisor terms bound g below by sums of 1/(p+1). Divergence of the reciprocal-prime sum ensures that every threshold is attained. Choose the least positive m with g(m) at least r. If m=1, the identity g(1)=1 settles the floor bound.

Otherwise let P be the largest prime divisor of m. Multiplicativity and g(p^a) <= p/(p-1), followed by the telescoping product over the integers from 2 to P, give g(m)<=P. Deleting one copy of P gives a positive q<m with g(m)<=g(q)(1+1/(P+1)). Minimality gives g(q)<r; since r<=P this yields r<=g(m)<r+1. Thus floor(g(m))=r. Every positive k with floor(g(k))=r also has g(k)>=r, proving leastness for both sets.

Krizek posed the source conjecture. Israel's prior observations include multiplicativity, the prime formula, divergence and existence of every level. The prime-power expansion is an elementary consequence of the divisor-sum definition. The common-minimum proof here is a repository derivation; the citation supplies the question and those observations. No integrality assertion about values above one or proposed numerical minima at later indices is included.

## References

- Truth anchor: `D5/S3/Factorization/ReciprocalSigmaThreshold.claim`
- Truth anchor: `D5/S3/Factorization/ReciprocalSigmaThreshold.g`
- Truth anchor: `D5/S3/Factorization/ReciprocalSigmaThreshold.result`
