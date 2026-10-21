---
bibkey: ball2022independent
authors: T. Ball, D. Galvin, C. Hyry, and K. Weingartner
year: 2022
title: "Independent set and matching permutations"
doi: 10.1002/jgt.22724
url: https://doi.org/10.1002/jgt.22724
claim: "Section 4, Question 4.6 asks which unimodal permutations arise from coefficients of products of nonnegative real linear factors."
strata_touched:
  - D5/S3/Combinatorics/RealRootedPermutations/Defs
  - D5/S3/Combinatorics/RealRootedPermutations/Result
license: citation-only
triage: anchor
---

# Independent set and matching permutations

## Locator

DOI: https://doi.org/10.1002/jgt.22724

Article URL: https://doi.org/10.1002/jgt.22724

T. Ball, D. Galvin, C. Hyry, and K. Weingartner, *Independent set and
matching permutations*, Journal of Graph Theory 99(1) (2022), 40–57.
Author manuscript: https://arxiv.org/abs/1901.06579, version 2.
The relevant locators are equations (1) and (4), Section 3 after
Lemma 3.1, Section 4 Question 4.6, and Problem 1.6.

## Source statement

Equation (1) associates a permutation $\pi$ of $[m]$ to a real sequence
$a_1,\ldots,a_m$ when

$$
a_{\pi(1)}\le\cdots\le a_{\pi(m)}.
$$

The constant polynomial coefficient is excluded. Equation (4) calls a
permutation of $[n]$ unimodal when, for $k=\pi(n)$,

$$
\pi^{-1}(1)<\cdots<\pi^{-1}(k),\qquad
\pi^{-1}(k)>\cdots>\pi^{-1}(n).
$$

The discussion after Lemma 3.1 observes:

> Because real-rooted polynomials have unimodal coefficient sequences, at most only the 2^{n−1} unimodal permutations of [n] can arise in this context.

The decreasing permutation $n(n-1)\cdots1$ is the example exhibited
there; its final value is $1$, so it satisfies (4).

Question 4.6 in Section 4 asks:

> Which unimodal permutations of [n] can arise via (1) from the coefficient sequence of a polynomial of the form (1+r₁x)(1+r₂x)⋯(1+rₙx) with rᵢ real and nonnegative?

Problem 1.6, attributed to Alavi–Malde–Schwenk–Erdős Problem 2, asks
which permutations are matching permutations of graphs. Question 4.6
is its polynomial relaxation. The source shows that only a vanishing
proportion of unimodal permutations can be matching permutations of
unweighted simple graphs.

## Source boundary

The formal reading uses degree $n$, hence all $r_i>0$, and orders
$a_1,\ldots,a_n$. Allowing all $r_i=0$ makes every listed coefficient
zero and admits every permutation under (1). The full-degree reading
retains the restriction to unimodal permutations in the source's
remark. The quotations and locators refer to the author manuscript;
the journal pagination and DOI identify the published article.
The formal equivalence and strict realization concern polynomial
coefficients, not unweighted graph realizability.
