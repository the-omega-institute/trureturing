---
bibkey: plewa2018laguerre
authors: Paweł Plewa
year: 2018
title: Sharp Hardy's type inequality for Laguerre expansions
doi: null
url: https://arxiv.org/abs/1810.08138v1
claim: The standard normalized Laguerre bulk estimate in equation (19) is uniform in degree and position; its parameter-one specialization controls the growing low-prime prefix of the actual centered Li row. The remaining middle interval and its signed joint estimate are not controlled.
strata_touched: []
license: citation-only
triage: anchor
---

# A classical uniform Laguerre bound for the actual Li prefix

The inspected source is [arXiv:1810.08138v1](https://arxiv.org/pdf/1810.08138v1),
20 pages. Its PDF SHA-256 is
`2251d296d1a523ba1873a990cf10c8d17f942f70792d80b6be0f8d5af42e59c6`.
The exact definitions and estimate were also read in the author's TeX.
Locators below refer to this manuscript. The journal metadata DOI
[10.2969/jmsj/84448444](https://doi.org/10.2969/jmsj/84448444)
is not used to assert that an uninspected publisher edition has identical
statements or numbering. The paper's main Hardy inequality is not needed
for this application.

Section 3's convolution-function definition and Section 4's
standard-function definition give

$$
\mathcal L_k^\alpha(u)
=\left(\frac{\Gamma(k+1)}{\Gamma(k+\alpha+1)}\right)^{1/2}
u^{\alpha/2}e^{-u/2}L_k^{(\alpha)}(u),\qquad\alpha>-1.
$$

Section 4, printed p.12, equation (19), gives the classical bulk bound

$$
|\mathcal L_k^\alpha(u)|\le C_\alpha(\nu u)^{-1/4},
\qquad \nu=\max(4k+2\alpha+2,2),\qquad
\nu^{-1}<u\le\nu/2.
$$

For fixed $\alpha$, the constant is uniform in $k,u$. The manuscript
attributes this estimate to Muckenhoupt, *Mean convergence of Hermite
and Laguerre series. II*, printed p.435, and Askey--Wainger,
*Mean convergence of expansions in Laguerre and Hermite series*,
printed p.699. Those original proofs are not independently audited here.
The estimate is directly reused, not reproved or counted as a new
orthogonal-polynomial result.

At $k=n-1$ and $\alpha=1$, the exact normalization and parameter map are

$$
\mathcal L_{n-1}^1(u)=\sqrt{u/n}\,e^{-u/2}L_{n-1}^{(1)}(u),
\qquad\nu=4n.
$$

Hence the cited estimate supplies

$$
|L_{n-1}^{(1)}(u)|\le Cn^{1/4}e^{u/2}u^{-3/4},
\qquad (4n)^{-1}<u\le2n.
$$

This range contains the entire growing interval
$\log2\le u\le\log N$, uniformly for integers $N/3\le n\le N$
and sufficiently large $N$. Thus the
[actual Li-prefix application](../Zeros/coffey2009stieltjes.md#cs9-a-classical-bound-pays-the-growing-low-prime-prefix)
uses a genuinely uniform bound, rather than a fixed-position asymptotic.
It dominates the finite prime sum by an integer sum and obtains an
$o(N)$ allowance for that specified prefix. No new prime-distribution
estimate, cancellation, numerical validation, Lean certification or
literature-priority claim is made. The remaining middle interval and
its common-source signed comparison, Robin and RH remain unresolved.
