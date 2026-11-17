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
  - D5/S3/Arith/CharacterSums/PascadiMinusRows
  - D5/S3/Arith/CharacterSums/PascadiOriginalCoefficients
  - D5/S3/Arith/CharacterSums/PascadiSingularResultant
  - D5/S3/Arith/CharacterSums/PascadiSingularFactorCover
  - D5/S3/Arith/CharacterSums/PascadiLocalizedFactor
  - D5/S3/Arith/CharacterSums/PascadiPrimeCubeSingularCover
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

## Repository prime-cube continuation (16 November 2026)

The new `PascadiMinusRows` module proves the original literal-box reduction
`Nminus ≤ 3 * Uminus + 8 * (2 * Y + 1)^2` for prime `p`, `X ≤ Y`,
`6 * Y < p^2`, and the same units `a₁,a₂` modulo `p^3`.
Odd letters lie in `[-X,X]`, even letters in `[-Y,Y]`; units are not multiplied
into the intervals. `Uminus` filters those same actual word solutions by
`p ∤ t*w`. The proof includes zero/nonunit rows, all-six-divisible tuples and
repeated endpoints. It uses exact four-equation equivalence for the existing
`sixReturnWord`, all three minors, cyclic charts and a direct finite pivot encoding.
The bound does not need the additional lower bound `p ≤ X`.

`PascadiOriginalCoefficients` constructs physical integer endpoints from lattice
coordinates and forms the literal coefficient functions of `L₀Q−LQ₀`.
Its root identity is derived from the actual original word equation, using
`β=V₁/R₁` and `α=−1/(g*t*R₁)`; it is not supplied as a polynomial-root hypothesis.
Literal coordinate bounds also give coefficient constant `C=3`, actual pencil
height `H=18`, and degree at most three. The lattice basis construction,
exceptional strata, physical multiplicities,
average/second-moment estimate, plus-center comparison and full original
prime-cube count remain unformalized here.

The four integrated singular-factor modules retain the proofs from the completed
research archive `pascadi-prime-cube-singular-cover-formalization-20261116`.
Necessary archived helpers are exposed publicly, replacing private-name elaborator
access. The original file identities are:

- `PascadiPrimeCubeSingularCover.lean`: SHA256 `b41d415ccf6f20adf7b23aad0d6ed2dd09bf9628cf2a0eb37faba3ceaa13572e`.
- `PascadiLocalizedFactor.lean`: SHA256 `3f4fdb232cd07f365c10aa8b032bf2f35396742aa6cbc4a51772a83494541b9f`.
- `PascadiSingularFactorCover.lean`: SHA256 `c2325493ea58a5a79ded8c4c26c14dc4813bbeac332f30d515346cb04cb282c4`.
- `PascadiSingularResultant.lean`: SHA256 `eb9f9c502221986f3b7f64263954614829ffd601da25470495669c1b2fcd2d54`.

The completed application proof was supplied as
`pascadi-prime-cube-actual-application-review-20261116/proof.tex`, SHA256
`c6e76b431b78245ce924f62084548f932f524c5908dbcdc3802bf8ef97275e0c`,
with author line “Independent mathematical source review”. This worker implements
the row reduction and starts actual coefficient realization; the supplied paper
proof and archived Lean endpoint have distinct provenance from this implementation.
These repository results are not attributed to Pascadi as published theorems and
do not claim to settle his full uniform conjecture.
