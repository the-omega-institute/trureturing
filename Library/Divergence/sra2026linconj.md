---
bibkey: sra2026linconj
authors: Suvrit Sra
year: 2026
title: On Lin's Arithmetic–Geometric Means Conjecture for Singular Values
doi: null
url: https://suvrit.github.io/papers/linconj/linconj-v1.pdf
claim: Theorem 1.1 proves Lin's weighted singular-value inequality for every weight; the proof uses an inertia identity and a scalar inequality.
strata_touched:
  - D5/S3/Quantum/Matrix/SharpWeightedLin
license: citation-only
triage: anchor
---

# On Lin's Arithmetic–Geometric Means Conjecture for Singular Values

## Verified locator

Source: https://suvrit.github.io/papers/linconj/linconj-v1.pdf.
DOI: null.

The checked source is hexagon:2610.00623v1, version 1, dated 8 October 2026.
It is a preprint posted on the author's page; it has no arXiv identifier and
no journal publication or peer review is recorded. The theorem and numbering
below follow the source PDF.

## Theorem 1.1

For positive semidefinite $A,B$ and $0\le t\le1$,

$$
\sigma_j\!\left(A^{2(1-t)}B^{2t}\right)^{1/2}
\le \lambda_j\!\left((1-t)A+tB\right),
\qquad j=1,\ldots,n.
$$

The source calls this Lin's conjecture and notes that $t=1/2$ is Drury's
theorem.

## The exponent family (1.3)

For every $q>0$, the source considers

$$
\sigma_j\!\left(A^{(1-t)/q}B^{t/q}\right)^q
\le \lambda_j\!\left((1-t)A+tB\right),
\qquad j=1,\ldots,n.
$$

The family is monotone in the exponent: validity at $q$ gives validity at
every larger exponent. Theorem 1.1 supplies the range $q\ge1/2$.

## Lemma 2.1: inertia identity

Let $H=H^*$ be invertible on a finite-dimensional Hilbert space, let
$J:P\to H$ be an isometric inclusion, and let $W\succ0$ on $P$. Put

$$
M=H+JWJ^*,\qquad G=W^{-1}+J^*H^{-1}J.
$$

Then

$$
 n_{\ge0}(M)=n_+(H)+n_{\le0}(G),
$$

where each count includes algebraic multiplicity and the subscripts denote
nonnegative, positive, and nonpositive eigenvalues, respectively.

## Lemma 2.2: scalar inequality

If $0<a\le b$, $a+b=1$, and $0\le x<1/a$, then

$$
 x^{4a}\le 1+4b^2\left(\frac1{1-ax}-\frac1b\right).
$$

Equality holds at $x=1$. Consequently, for every probability measure $\mu$
supported on $[0,1/a)$,

$$
\left(\int x^{4a}\,d\mu(x)\right)^{1/(4b)}
\le b\int\frac{d\mu(x)}{1-ax}.
$$

The proof of Theorem 1.1 combines this scalar estimate with the inertia
identity and a spectral-measure estimate. The repository settlement retains this inertia method and replaces the
scalar step to obtain the exponent $q=2t(1-t)$, with $a=1-t$ and $b=t$.
That weighted endpoint is a repository conclusion, not the exponent range
asserted in Sra's Theorem 1.1.
