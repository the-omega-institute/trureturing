---
bibkey: garciavolcic2025hunter
authors: S. R. Garcia and J. Volčič
year: 2025
title: A noncommutative generalization of Hunter's positivity theorem
doi: 10.1090/proc/17480
url: https://arxiv.org/abs/2503.12376v2
claim: 'Let $n,d\ge 2$. For all tuples of hermitian operators $X_1,\dots,X_n$ on a Hilbert space, $\ker \left(H_{2d}(X_1,\dots,X_n)-\mu_{n,d}(X_1^{2d}+\cdots+X_n^{2d})\right) = \ker X_1\cap\cdots\cap \ker X_n.$'
strata_touched:
  - D5/S3/Analytic/Hunter/NCHunterPositivity
  - D5/S3/Analytic/Hunter/NCHunterKernelRigidity
license: citation-only
triage: anchor
---

# The noncommutative Hunter bound

## Verified locator

DOI: https://doi.org/10.1090/proc/17480

Source: https://arxiv.org/abs/2503.12376v2

Theorem 1.1(ii), pages 2–3, gives the sharp positivity constant.
Example 4.4 and Conjecture 4.5 are on page 11 of arXiv v2.
Conjecture 4.6 is on page 12.
The published article is in Proceedings of the American Mathematical Society
154(2), pages 585–597.

## Source definitions

“Let $\sigma:\mathbb R[x_1,\ldots,x_n]\to\mathbb R\langle x_1,\ldots,x_n\rangle$
denote the linear map”

$$
\sigma(m):=\frac{1}{|\alpha^{-1}(m)|}\sum_{w\in\alpha^{-1}(m)}w.
$$

“The noncommutative complete homogeneous symmetric (NCHS) polynomial of
degree $d$ in $n$ (noncommuting) variables is”

$$H_d(x_1,\ldots,x_n):=\sigma\big(h_d(x_1,\ldots,x_n)\big).$$

The coefficient of a word of length $k$ with multiplicities $m_i$ is
$\prod_i m_i!/k!$, the reciprocal of its actual abelianization-fibre size.
The Lean carrier reindexes letters by `Fin n` and uses the frozen occupation
map to count them; evaluation is the ordered product, not a commutative one.

## Conjecture 4.5

“Let $n,d\ge 2$. For all tuples of hermitian operators $X_1,\dots,X_n$ on a Hilbert space,”

$$
\ker\left(H_{2d}(X_1,\dots,X_n)-\mu_{n,d}(X_1^{2d}+\cdots+X_n^{2d})\right)
=\ker X_1\cap\cdots\cap\ker X_n.
$$

The formal statement uses bounded complex-linear operators on a complete
complex inner-product space. Unbounded self-adjoint operators and their domain
questions are outside this carrier.

## Scope

The source's Theorem 1.1(ii) supplies the sharp positivity statement; its
optimality assertion is attributed to the source and is not a new formal
statement here. The proof uses a finite factorial Gram identity instead of
simplex integration. This is a proof representation and does not claim that
the scalar Vandermonde identity is new.

Conjecture 4.6 concerns entrywise nonnegative factorizations, a stronger property
than positive semidefiniteness. It is untouched by the kernel proof.

## Scalar factorial identity

The shifted scalar identity follows from Chu–Vandermonde,
NIST Digital Library of Mathematical Functions, equation 15.4.24:
https://dlmf.nist.gov/15.4.E24 . In
$F(-a,-b;g+1;1)=(g+1+b)_a/(g+1)_a$,
expand the terminating series and multiply by $(a+g)!(b+g)!/g!$.
Taking products over letters gives the finite factorial Gram representation.
Neither the scalar identity nor this product construction is claimed original.
