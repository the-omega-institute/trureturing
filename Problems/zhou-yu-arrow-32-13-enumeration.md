---
slug: zhou-yu-arrow-32-13-enumeration
bibkey: zhou2026arrow
doi: 10.48550/arXiv.2609.29392
url: https://arxiv.org/abs/2609.29392v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result
---

# Enumeration of the Arrow Pattern (32; 1 → 3)

## Problem

Robin D.P. Zhou and Xinyang Yu, *Arrow-Wilf equivalences and enumerative results for short arrow
patterns*, arXiv:2609.29392v1, abstract:

> Together with earlier work of Archer and Laudone, this leaves only (32;1→3) unresolved for |ν|≤2, which we pose as an open problem.

Here `S_n(32; 1 → 3)` consists of permutations of `1, …, n` avoiding the arrow pattern in the
paper's sense: the selected values have the required order in the one-line word, and the prescribed
arrow holds in `π̂ = θ⁻¹(π)`.

## Motivation

Write `a_n = |S_n(32; 1 → 3)|`, with `a_0 = 1`, and `F(x) = Σ_{n≥0} a_n x^n`. The theorem
`D5/S3/Combinatorics/ArrowThirtyTwoOneThree.result` establishes

`1 + (3x − 2)F + (1 − x)(1 − 2x)F² + x³F³ = 0`.

Among integer formal power series satisfying this cubic, `F` is uniquely determined by
`F(0) = 1` and `[x]F = 1`. The initial counts for `n = 0, …, 8` are
`1, 1, 2, 5, 15, 51, 190, 757, 3171`.

## Gap

Pre-registration issue 11059 records the literature screen. The arXiv record has no later paper on
arrow patterns, OEIS has no entry for `1, 2, 5, 15, 51, 190, 757, 3171`, and the repository had no
result for this enumeration before the theorem above. These are bounded negative findings, not a
claim about all mathematical literature.

## Route

1. An avoider is characterized by its inverse Foata edges: whenever `a < c < π̂(a)`, the value `c`
   must precede `π̂(a)` in the one-line word. For words of distinct values, a classical `132`
   occurrence exists exactly when an adjacent `13-2` occurrence exists.
2. Split an avoider at its largest value. The letters of its final cycle form a selected set; its
   last letter is the largest selected letter, and the preceding order avoids `132`. Missing selected
   values separate the prefix into ordered value intervals. Conversely, interval avoiders and a
   `132`-avoiding final-cycle order reconstruct a unique avoider.
3. A final cycle with `k ≥ 1` other letters contributes `C_{k−1}` times the coefficient of
   `x^{n−1−k}` in `F^{k+1}`; a singleton final cycle contributes `a_{n−1}`. The resulting recurrence,
   together with `C(z) = 1 + zC(z)²`, gives `F = 1 + xF + (xF)² C(xF)`, hence the cubic above.
4. If two integer formal series satisfy the cubic and both have constant and linear coefficients
   equal to one, the difference of their cubic equations factors by their series difference. The
   remaining factor has first nonzero coefficient `−1` at degree one, so it cannot annihilate a
   nonzero series difference. Thus the distinguished branch is unique.

## Falsifier

The enumeration statement would fail if some `n` had a different avoidance count from the
coefficients of the distinguished cubic branch. Fixing only `F(0) = 1` does not characterize that
branch: the cubic also has a formal solution beginning `1 + 2x + 3x² + x³ − 16x⁴ + …`.
The conclusion depends on the paper's arrow-containment convention and the inverse Foata cycle map;
changing either changes the class being counted.

## Evidence

The count recurrence is obtained from the final-cycle bijection, and the cubic follows as a formal
power-series identity over the integers. Independent exhaustive enumeration through `n = 11`
agrees with the edge criterion, reconstruction, refined counts, and cubic coefficients.

## Triage

`theorem`; the open question is stated in the abstract of arXiv:2609.29392v1. The result is
quantified over every size and is not a bounded enumeration.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv, OEIS, and repository checks recorded above. It does
not establish a worldwide priority claim.
