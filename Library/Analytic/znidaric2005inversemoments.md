---
bibkey: znidaric2005inversemoments
authors: "Marko Žnidarič"
year: 2005
title: "Asymptotic expansion for inverse moments of binomial and Poisson distributions"
doi: "10.2174/1876527000901010007"
url: "https://arxiv.org/abs/math/0511226v1"
claim: "Inverse binomial moments and shifted inverse moments are classical tools; a shifted finite moment bounds the source-scale averages used with actual FIB Newton coefficients."
strata_touched: []
license: "Citation only; no source text is reproduced."
triage: anchor
---
<!-- GID: D5/L/Analytic/znidaric2005inversemoments -->
# Inverse moments and the retained zero row

The retained primary version is arXiv:math/0511226v1, published
2005-11-09T12:47:23Z. Its eight-page PDF has SHA256
`f816f78cd2ec3abd4f9829aaf3191a2cd41a2dd22fe259b53d62d5fae2e921d5`.
The arXiv metadata links the 2009 journal version, The Open Statistics &
Probability Journal 1, 7–10, with the DOI above. This note uses preprint
locators, not journal pagination. Source TeX supplies the mathematical symbols
where the PDF extractor reports missing font-encoding support.

The introduction defines positive binomial inverse moments by summing over
$1\le j\le n$. Its equation (2) is the unnormalized positive-binomial moment;
the factor $1-(1-z)^n$ accounts for conditioning away the zero value.
Those conventions differ from an expectation over the complete binomial law.

PDF page 2 explicitly discusses Chao and Strawderman's shifted inverse
moments $\mathbb E[(X+a)^{-r}]$, with simple expressions for integer
$a\ge1$ and $r=1$. The reference on PDF page 8 identifies their paper as
*Negative moments of positive random variables*, Journal of the American
Statistical Association 67 (1972), 429–431. The 1972 paper is cited through
this discussion; its body has not been independently inspected here.

For $J\sim\operatorname{Bin}(k,z)$, $0<z\le1$, the elementary finite
identity relevant to the project is

$$
\mathbb E\frac1{J+1}
=\frac{1-(1-z)^{k+1}}{(k+1)z}.
$$

It retains $J=0$, and includes $k=0$ and $z=1$. It follows by replacing
$\binom kj/(j+1)$ with $\binom{k+1}{j+1}/(k+1)$ and applying the binomial
theorem. The identity is a classical tool, not a claimed new theorem of the
preprint. Applying Jensen's inequality to $x^p$, $0\le p\le1$, gives

$$
\mathbb E[(J+1)^{-p}]
\le \bigl(\mathbb E[(J+1)^{-1}]\bigr)^p
\le ((k+1)z)^{-p}.
$$

This is a uniform finite inequality rather than an asymptotic expansion at
fixed $z$. It can therefore be used when the FIB source-scale parameter
$z=d^{-2}$ varies with the source index. The paper's positive-binomial
asymptotic theorem is not substituted for this full-law inequality, and no
Möbius cancellation or critical coefficient decay follows merely from it.

The finite binomial identity and the Jensen specialization have been checked
by direct transient application of pinned mathlib. No named wrapper is added
to the formal library, and that check does not cover an infinite coefficient
transport or prove RH.
