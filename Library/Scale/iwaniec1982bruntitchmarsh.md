---
bibkey: iwaniec1982bruntitchmarsh
authors: Henryk Iwaniec
year: 1982
title: On the Brun-Titchmarsh theorem
doi: 10.2969/jmsj/03410095
url: https://www.jstage.jst.go.jp/article/jmath1948/34/1/34_1_95/_article
claim: A published all-centre short-interval upper count supplies a smaller first-layer capacity at the original Robin selector's paid lag scale.
strata_touched: []
license: citation-only
triage: anchor
---

# A fixed-exponent count for every sufficiently large centre

The primary is *On the Brun-Titchmarsh theorem*, *Journal of the
Mathematical Society of Japan* **34**(1) (1982), 95--123,
[DOI 10.2969/jmsj/03410095](https://doi.org/10.2969/jmsj/03410095).
Section 6 starts on printed p.120. Theorem 14 and the final paragraph
of printed p.121 are the inputs used here. The inspected
[journal PDF](https://www.jstage.jst.go.jp/article/jmath1948/34/1/34_1_95/_pdf)
has SHA-256
`95f2cc37016f1dac53967d964f1505ab5f369721271176749d8ad5107f67c22e`.

Theorem 14 states that, for fixed $0<s<1$, there is $\nu(s)>s$
such that, for every fixed $\varepsilon>0$ and all
$x>x_0(\varepsilon,s)$,

$$
\pi(x+x^s)-\pi(x)
<\frac{(2+\varepsilon)x^s}{\nu(s)\log x}.
$$

The final paragraph specifies $\nu(s)=(1+s)/2$ for $s>1/2$.
Thus, for any fixed $1/2<s<1$ and $c>4/(1+s)$, one common
real start gives

$$
\pi(x+x^s)-\pi(x)\le c\frac{x^s}{\log x}
$$

for every centre beyond that start. The exponent-pairs conjecture
printed separately on the same page is not an assumption of this
input. There is no exceptional-centre selection or RH premise.

Section 6 explicitly states its results without proofs. This note
records the published statement and its applicability, not an
independent proof of that statement or a Lean verification. No
numerical value of the common start is certified.

The [price-gap consumer](../Estimation/trureturing2026pricegapconvexity.md#published-uniform-counts-sharpen-capacity-at-the-actual-lag-scale)
tiles each actual first-layer prefix by these fixed-exponent intervals.
Its last overhanging block is paid as $O(B^s)$, every prime keeps its
own logarithmic weight, and the existing full higher-layer mass is
retained. Its stock coefficient and joint lower margin are project
applications of this count and existing competitor costs, not
theorems attributed to Iwaniec. No best-known-constant or originality
claim is made.
