---
bibkey: pascadi2025nonabelianamplification
authors: Alexandru Pascadi
year: 2026
title: Non-abelian amplification and bilinear forms with Kloosterman sums
doi: null
url: https://arxiv.org/abs/2511.08445v2
claim: Conjecture 6.1 gives a uniform upper bound for alternating T,S return words in PSL_2(Z/cZ); Proposition 6.2 gives a weaker q=6 bound and proves the conjecture only in some parameter ranges.
strata_touched:
  - D5/S3/Arith/CharacterSums/PascadiSixWordFiber
license: source-reference
triage: anchor
---

# Pascadi's non-abelian amplification

Pascadi studies alternating return words

$$T^{a_1h_1}ST^{a_2h_2}S\cdots T^{a_1h_{q-1}}ST^{a_2h_q}S=I$$

in $\mathrm{PSL}_2(\mathbb Z/c\mathbb Z)$, for even $q$, units $a_1,a_2$ modulo $c$, and
$1\le H_1\le H_2\ll c$. Conjecture 6.1 predicts the bound

$$c^{o(1)}\left(H_2^{(q-2)/2}+\frac{(H_1H_2)^{q/2}}{c^3}\right).$$

For $q=6$, Proposition 6.2 proves the weaker estimate

$$c^{o(1)}\left(H_2^2+\frac{(H_1H_2)^2}{c}\right),$$

and notes ranges where the conjectured estimate follows. The median-range six-letter case
remains open in the source version.

The repository module `D5/S3/Arith/CharacterSums/PascadiSixWordFiber` formalizes the
entrywise compatibility equations for a fixed central scalar return and proves that each
fixed-middle completion fiber has period
$N=c/\gcd(c,(1-a_1a_2h_2h_3).\mathrm{val})$. For every $c>0$, units $a_1,a_2$ in
$\mathbb Z/c\mathbb Z$, central scalar $\gamma$ with $\gamma^2=1$, fixed
$h_2,h_3,h_5,h_6$ in $\mathbb Z/c\mathbb Z$, and $H\in\mathbb N$, it bounds the
actual return solutions by

$$\#\{(h_1,h_4)\in\{0,\ldots,H-1\}^2:
\mathrm{sixReturnWord}(a_1,a_2,h_1,h_2,h_3,h_4,h_5,h_6)=\gamma I\}
\le (\lfloor H/N\rfloor+1)^2.$$

Here the natural coordinates are reduced modulo $c$ only in the matrix product.
The bound includes $H=0$, arbitrary $H$ beyond $c$, composite moduli, and the
singular stratum $1-a_1a_2h_2h_3=0$, where $N=1$. The period is used to make the
coordinatewise quotient map injective on actual solutions. Summing over middle
coordinates with the strength required by Conjecture 6.1 remains open.

## Verified locator

Source: <https://arxiv.org/abs/2511.08445v2>, Section 6: Conjecture 6.1,
bound (6.2), and Proposition 6.2, weaker $q=6$ bound (6.3), including the
following remark on the parameter ranges where the conjecture follows.
