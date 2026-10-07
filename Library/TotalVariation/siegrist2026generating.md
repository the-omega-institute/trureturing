---
bibkey: siegrist2026generating
authors: Kyle Siegrist
year: 2026
title: "Random: Probability, Mathematical Statistics, Stochastic Processes"
doi: null
url: https://www.randomservices.org/random/
claim: The probability generating function gives P(N even)=(1+G(-1))/2; for a binomial sum of d independent Bernoulli(p) bits, G(t)=(1-p+pt)^d, and conditioning on a positive-probability event defines a probability law.
strata_touched:
  - D5/S3/TotalVariation/ParityKernelMasses
  - D5/S3/TotalVariation/TreeParityKernel
license: CC-BY-2.0
triage: anchor
---

# Bernoulli parity and conditional normalization

## Verified locator

The source is Kyle Siegrist's online textbook
[*Random: Probability, Mathematical Statistics, Stochastic Processes*](https://www.randomservices.org/random/).
The bibliographic year identifies the consulted online version; the pages do
not state a publication year. Its home page specifies
[CC BY 2.0](https://creativecommons.org/licenses/by/2.0/) and requires attribution
and a link to the home site. No DOI is supplied by the source.

The following named sections and anchored statements supply the identities:

- [Generating Functions, The Probability Generating Function, `pgf4`](https://www.randomservices.org/random/expect/Generating.html#pgf4)
  states `P(N is even) = (1 + G(-1))/2` and proves it by adding `G(1)` and `G(-1)`.
- [The Binomial Distribution, Moments, `mom3`](https://www.randomservices.org/random/bernoulli/Binomial.html#mom3)
  states `G(t) = (1-p+pt)^d` for the sum of `d` independent Bernoulli(`p`) bits,
  for every real `t`.
- [Conditional Probability, `dfn`](https://www.randomservices.org/random/prob/Conditional.html#dfn)
  defines `P(A | B) = P(A intersect B)/P(B)` when `P(B) > 0`; its Basic Theory
  also proves that this conditional law is a probability measure.

These HTML statements, their proofs, the author metadata and the home-page
license identify the source and are the verification method for this note.
The mathematical descriptions here are adapted from that source with attribution.

For a bit vector `x`, let `h(x)` count its occupied coordinates. The even
formula and its complementary odd formula give

$$
\mathbb P(h(X)\equiv M\pmod 2)
=\frac{1+(-1)^M(1-2p)^d}{2}.
$$

For positive natural `d` and `M`, take `p = M/(2M+d)`. Then
`1-2p = d/(2M+d)` lies strictly between zero and one, so the displayed
probability `p_e` is positive. The vector mass conditioned on this event is

$$
Q(x)=\begin{cases}
p^{h(x)}(1-p)^{d-h(x)}/p_e,&h(x)\equiv M\pmod 2,\\
0,&\text{otherwise}.
\end{cases}
$$

It is nonnegative and sums to one by the cited conditional-probability law.
This is the textbook identity at the displayed parameter choice, not a claim
that the conditioned coordinates remain independent. The source does not
identify this law with an actual ordered-tree parity law or supply the finite
total-variation comparison between that law and uniform weak compositions.
