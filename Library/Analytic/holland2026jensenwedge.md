---
bibkey: holland2026jensenwedge
authors: Jonathan Holland
year: 2026
title: A new hyperbolicity wedge and a joint semicircle limit for Jensen polynomials of Riemann's xi-function
doi: null
url: https://arxiv.org/abs/2608.08682v1
claim: Theorem 1.1 states a joint degree-shift hyperbolicity region for the actual xi coefficients; its sufficient condition excludes every positive degree at zero shift.
strata_touched: []
license: citation-only
triage: anchor
---

# A joint degree-shift Jensen supplier

The primary is [arXiv:2608.08682v1](https://arxiv.org/html/2608.08682v1),
Jonathan Holland, *A new hyperbolicity wedge and a joint semicircle limit
for Jensen polynomials of Riemann's xi-function*. The source locators
below refer to this version. Its coefficient definitions, Theorem 1.1,
Proposition 2.2, Lemmas 8.1 and 9.1, and the completion of the argument
in section 10 were inspected. The results remain public-preprint
statements; this note supplies neither a complete independent proof
audit nor Lean verification. No source text is vendored.

## Source coefficients and the joint region

Section 1 uses the standard completed function

$$
\xi(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s),
\qquad
\xi(1/2+z)=\sum_{k\ge0}\frac{\Gamma_k}{k!}z^{2k}.
$$

Here $\Gamma_k$ denotes the paper's positive coefficient $\gamma(k)$,
not a value of the Euler Gamma function. For integers $d,n\ge0$ it defines

$$
J^{d,n}(X)=\sum_{k=0}^{d}\binom dk\Gamma_{n+k}X^k.
$$

Theorem 1.1 states that there is an absolute constant $K>0$ such that

$$
d\ge1,\quad n\ge0,\quad n^3\log^2(n+2)\ge Kd^5
\quad\Longrightarrow\quad
J^{d,n}\text{ has }d\text{ distinct negative real roots}.
\tag{JW}
$$

Equivalently the sufficient region has
$d\le K^{-1/5}n^{3/5}\log^{2/5}(n+2)$. It permits degree and shift
to grow together. The existence of $K$ does not supply a numerical
threshold or a finite-input certificate. The statement is unconditional
within its sufficient region; it is not a statement for every pair
$(d,n)$.

The source's proof compares the actual coefficient ratios with a
positive-root model formed from Laguerre and Jacobi families and
finite-free multiplicative convolution. Proposition 2.2 supplies its
multiplier stability step; the comparison matches coefficients through
index four. Lemma 8.1 bounds the remaining multiplier error by

$$
O\!\left(\frac{d^{5/2}}{n^{3/2}\log(n+2)}\right),
$$

on its specified complex neighborhood, and Lemma 9.1 controls derivative
ratios at the comparison model's critical points. Section 10 combines
these estimates to obtain (JW). These are source results to reuse,
not new polynomial identities or estimates of this repository.

The five coefficient matching conditions concern the actual xi sequence.
They do not identify the five Zeckendorf inclusion modes
`[null,2,3,2 5,5]` with these moments or supply an estimate through that
encoding. Such an application would require its own parameter and
inequality correspondence.
