# The degree boundary in Cigler's Conjecture 16

## Abstract

The literal exact-degree requirement in Cigler's v2 Conjecture 16 fails at k=1 and m=0.

The source is Johann Cigler's arXiv:2308.07642v2, Section 3, Conjecture 16, equation (30), on page 10. Its Catalan coefficients and determinant conventions appear in equations (1) and (2) on page 1; reciprocity and second polygonal numbers are defined on page 9. The conjecture is interpreted coefficientwise over the complex numbers. There is no analytic convergence hypothesis.

**Definition 1.1 (The actual Catalan series).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanSeries`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a commutative ring R, C(x) is Mathlib's natural Catalan series with coefficients cast into R: its coefficient at n is the Catalan number binom(2n,n)/(n+1). In particular its constant coefficient is one. The sequence is not defined by a Hankel evaluation or a conjectured numerator.

**Definition 1.2 (Convolution coefficients and negative indices).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanPowerCoeff`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanPowerCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a natural r and an integer t, C_{r,t} is the coefficient at t of C(x)^r when t is nonnegative, and zero when t is negative. The claim uses only positive r. This is the source's defining convolution interpretation; no closed-form coefficient bridge is assumed.

**Definition 1.3 (Every finite Hankel determinant).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankel`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a commutative ring R, a natural r, an integer m and a natural N, D_{r,m}(N) is the determinant of the matrix C_{r,i+j+m}, with i and j ranging through Fin N. Negative shifts retain their integer meaning. The empty determinant D_{r,m}(0) is one.

**Definition 1.4 (The full determinant generating series).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankelSeries`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankelSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For R, r and m as above, F_{r,m}(x) has coefficient D_{r,m}(N) at every natural N. It is the entire formal series, with no truncation and no selected determinant sizes.

**Definition 1.5 (Second polygonal numbers).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.polygonalNumber`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.polygonalNumber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For integers j and t, pi_j(t) is t((j-2)t+(j-4))/2, evaluated in the rationals. The source uses j at least three. Thus pi_3(t)=t(t-1)/2, including pi_3(0)=0; the subtraction j-4 is not truncated natural subtraction.

**Definition 1.6 (The product in equation (30)).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.numeratorSeries`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.numeratorSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a commutative ring R and integers k and m, the numerator series is (1+(-1)^k x^(2k-1))^(binom(k+m,2)+1) times F_{2k-1,m}(x), using natural conversions for its exponents and binomial argument. In the claimed range k is at least one and m is at least 1-k: consequently k, 2k-1 and k+m are positive, so every such conversion preserves its integer value. The shift m is never converted to a natural.

**Definition 1.7 (Palindromicity at actual degree).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.palindromic`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.palindromic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a complex polynomial Q of actual degree d, palindromicity means x^d Q(1/x)=Q(x) at every nonzero complex x. The exponent is Q.natDegree, which equals the actual degree when Q is nonzero. The exact-degree clause below excludes the zero polynomial.

**Definition 1.8 (Skew palindromicity at actual degree).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.skewPalindromic`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.skewPalindromic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For a complex polynomial Q of actual degree d, skew palindromicity means x^d Q(1/x)=-Q(x) at every nonzero complex x, with the same actual-degree convention.

**Definition 1.9 (The whole literal Conjecture 16).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

For every integer k at least one and every integer m at least 1-k, there exists a complex polynomial Q such that the full numerator series equals Q and its actual degree is pi_{2k+1}(m+k-1)+k. Formally, there is a natural d with Q.degree=d and d equal to that rational expression; this is an exact degree equality and implies Q is nonzero. Every Q is either palindromic or skew palindromic. It is palindromic if k is 1 modulo 4 and m is even, if k is 3 modulo 4 and m is odd, and if k is 0 or 2 modulo 4 and m is 0 or 1 modulo 4. These are implications, with no converses or additional sign rule. All permitted negative shifts and the boundary k=1 remain in the claim.

**Theorem 1.10 (The literal conjecture is false).**

Lean statement: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-sixteen-literal-numerator-degree` (refuted) by `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-sixteen-literal-numerator-degree","declaration_gid":"D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2023). *Some experimental observations about Hankel determinants of convolution powers of Catalan numbers*. DOI: [10.48550/arXiv.2308.07642](https://doi.org/10.48550/arXiv.2308.07642). URL: <https://arxiv.org/abs/2308.07642v2>.

*Commentary.*

Take k=1 and m=0. The multiplier is 1-x and the demanded degree is pi_3(0)+1=1. The true empty determinant and the true singleton determinant are both one: the latter is C_{1,0}, the constant coefficient of the actual Catalan series. Therefore the linear coefficient of (1-x)F_{1,0} is D_{1,0}(1)-D_{1,0}(0)=0. Polynomial-to-series coefficient compatibility makes Q's linear coefficient zero, whereas exact degree one makes it nonzero. This contradicts one conjunct of the whole universal assertion. The coefficient obstruction is proved over every commutative ring, and thus also holds directly for integer, rational and real polynomials. It does not depend on a rational-only restriction or any convention for the degree of zero.

Equation (6), on page 2, already records the well-known all-order identities D_{1,0}(N)=D_{1,1}(N)=1. No new determinant evaluation is asserted. The paragraph after (30) calls k=1 'not optimal' and prints Q_{1,m+1}(x)=(x-1)^(m+1)P_{2,m}(x). In the m at least zero range inherited from (29), that shifted relation does not include Q_{1,0}; it neither removes that boundary from the conjecture nor retracts its exact degree equality. Its sign is retained as printed and is not used in the proof. The different v1 Conjecture 16 becomes v2 Conjecture 18. No repaired degree bound, k at least two conjecture, or worldwide priority is asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanPowerCoeff`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.catalanSeries`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankel`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.hankelSeries`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.numeratorSeries`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.palindromic`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.polygonalNumber`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.skewPalindromic`
