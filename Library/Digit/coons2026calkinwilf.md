---
bibkey: coons2026calkinwilf
authors: Michael Coons
year: 2026
title: "The Calkin–Wilf problems on ℓ-ary partition functions, arXiv:2611.08109v1"
doi: null
url: https://arxiv.org/html/2611.08109v1
claim: "Section 3 asks whether the logarithmic limsup growth exponent strictly increases with every adjacent multiplicity bound k,k+1 for k at least ell-1."
strata_touched:
  - D5/S1/Digit/CoonsAdjacentGrowthRefutation
  - D5/S1/Digit/DigitCapPowerGF
  - D5/S1/Digit/DigitCapSubcritical
  - D5/S1/Digit/DigitCapLeastCap
license: CC-BY-4.0
triage: anchor
---

# Coons's adjacent-multiplicity growth question

## Verified locator

- URL: https://arxiv.org/html/2611.08109v1
- Version: arXiv:2611.08109v1, Michael Coons, *The Calkin–Wilf problems
  on ℓ-ary partition functions*.
- Count: Section 1, opening definition; Section 2, opening generating product.
- Question: Section 3, “Further remarks”, final display and the immediately
  following quantifier, before Acknowledgements.
- Critical caps: Theorem 2, its proof's display
  $B_{\ell^m-1,\ell}(z)=\prod_{j=0}^{m-1}(1-z^{\ell^j})^{-1}$ following equation (3),
  and equation (4),
  $b_{\ell^m-1,\ell}(n)=\frac{n^{m-1}}{\ell^{m(m-1)/2}(m-1)!}(1+O(1/n))$.

## Attribution and license

The primary HTML explicitly displays “License: CC BY 4.0”. The license is
[Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/).
The question quotation below is attributed to Michael Coons and the versioned
source above. Mathematical alttext is transcribed into Markdown display
notation; the surrounding explanations and counterexample exposition are
repository-authored. No complete source text or third-party PDF is reproduced.
The license statement applies to Coons's source, not automatically to works
in its bibliography.

## Exact question and count convention

Section 3 asks:

> As a generalisation, we ask whether it is always the case that

$$
\limsup_{n\to\infty}\frac{\log b_{k,\ell}(n)}{\log n}
<
\limsup_{n\to\infty}\frac{\log b_{k+1,\ell}(n)}{\log n},
$$

> for all $k\geqslant\ell-1$?

Here $\ell$ is an integer radix at least two. Section 2 specifies

$$
B_{k,\ell}(z)=\sum_{n\geq0}b_{k,\ell}(n)z^n
=\prod_{j\geq0}\left(1+z^{\ell^j}+\cdots+z^{k\ell^j}\right).
$$

Thus $b_{k,\ell}(n)$ counts multiplicity functions $a:\mathbb N\to\mathbb N$
of finite support, with $a(i)\leq k$ and $\sum_i a(i)\ell^i=n$.
Each function is counted once; adding trailing zeros creates no new partition.
The empty partition gives $b_{k,\ell}(0)=1$. Ordinary radix digits ensure
positivity when $k\geq\ell-1$.

The introductory expansion prints $a_m\ell^n$ in its general term. The
prose's powers-of-$\ell$ definition and Section 2's product specify the
intended weight $\ell^m$. The introduction also begins with $k,\ell\geq2$,
whereas the final question explicitly uses $k\geq\ell-1$. The same count
definition extends to $(\ell,k)=(2,1)$, which is retained in the universal
statement. These conventions are explicit interpretations of the displayed
question and product, without a claim of additional author confirmation.

The source does not specify a limsup codomain. The corresponding formal
quantity is the extended-real infimum of all natural tail suprema,
$\inf_{N\geq2}\sup_{n\geq N}\log b_{k,\ell}(n)/\log n$.
It assumes neither a finite exponent nor a selected subsequence in place of
the entire natural tail.

The next source sentence, “What about the limit inferiors?”, is a separate
question. The preceding discussion of CW2 asks about the first multiplicity
bound giving linear maximal growth. Neither is identified with the displayed
strict-adjacency question.

## Counterexample and applicability

The corresponding [problem dossier](../../Problems/coons-strict-adjacent-multiplicity-growth.md)
gives the source-to-formal correspondence and proof mechanism. At radix four,
the bounds five and six both have logarithmic limsup exponent $1/2$.
An upper bound holds at every natural input, and distinct binary carry
choices attain $2^m$ representations at the repunit
$R_m=\sum_{i=0}^{m}4^i$. Cofinality of these repunits proves a lower bound
for every whole tail. Equality of the two exponents refutes the universal
strict inequality; it asserts no liminf value or linear-growth threshold.

## Bounded literature coverage

The inspected fulltexts are the public 19-page Calkin–Wilf *Binary partitions
of integers and Stern-Brocot-like trees* and the eight-page published
Coons–Spiegelhofer *The Maximal Order of Hyper-(b-ary)-expansions*, Electronic
Journal of Combinatorics 24(1), #P1.15 (2017),
[DOI 10.37236/5441](https://doi.org/10.37236/5441).
Calkin–Wilf Section 10 discusses general bounded multiplicities, a linear
threshold and a distinct normalized single-family limsup question.
Coons–Spiegelhofer's maximal-order theorem concerns digits $0,\ldots,b$
at radix $b$, with $s_b(n)$ counting expansions of $n-1$. Neither inspected
fulltext was found to settle this exact universal adjacent-bound question.
That finding is limited to the inspected texts.

The obtained Calkin–Wilf copy has a cover dated January 12, 1998; its identity
with the August 5, 2009 update cited by Coons is unverified. Bruce Reznick's
*Some Binary Partition Functions*, Progress in Mathematics 85 (1990),
pp. 451–477, [DOI 10.1007/978-1-4612-3464-7_29](https://doi.org/10.1007/978-1-4612-3464-7_29),
was identified bibliographically but its chapter fulltext was not obtained.
No negative finding about that chapter's theorems follows. The full Coons
joint-spectral-radius paper, Coons–Tyler paper, underlying Defant paper and
subsequent citing literature are not covered by these fulltext readings.
No worldwide openness, exhaustive absence, novelty or priority claim is made.

## Subcritical caps (CW2)

Section 1 lists CW2: "Is k = ℓ²−1 the first time we get linear maximum growth?". Section 3,
third paragraph, notes that "it would be enough to show that the maximal growth of
b_{ℓ²−2,ℓ}(n) is strictly sublinear". The general bound formalized in `DigitCapSubcritical` is
not asserted in this source: for k ≤ ell^r − 2 and n < ell^(m+1),
b(k, ell, n) ≤ Q^(m mod 2) H^⌊m/2⌋ with Q = ell^(r−1) and H = Q² − Q/ell, so
b(k, ell, n) = O(n^((log_ell H)/2)) with (log_ell H)/2 < r − 1. It is Theorem 1, equation (3),
of the outreach note registered in the-omega-institute/trureturing-requests#300, and it
improves `DigitCapQuotientBound.count_le_pow` (Q^m) for caps at most ell^r − 2. Its case r = 2 is
exactly the sufficient condition quoted above.

The least cap whose upper exponent reaches r − 1 is ell^r − 1 (`DigitCapLeastCap.least_cap`):
the cap ell^r − 1 grows like n^(r−1) by the product formula of Theorem 2, and every smaller cap
is subcritical. With the exact count n/ell + 1 at ell² − 1, the case r = 2 answers CW2, which
Coons lists as open, in the sense that no smaller cap has upper exponent at least 1; this is
Corollary 2 of the outreach note registered in the-omega-institute/trureturing-requests#301.
Separately, `DigitCapLeastCap.least_linear_min` formalizes CW3, "Is k = ℓ²−1 the first time we
get linear minimum growth?", which Coons answers in his Theorem 1: ell² − 1 is the least cap
with c·n ≤ b(k, ell, n) for all large n.
