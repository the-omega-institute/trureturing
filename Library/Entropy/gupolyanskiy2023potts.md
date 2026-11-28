---
bibkey: gupolyanskiy2023potts
authors: Yuzhou Gu and Yury Polyanskiy
year: 2023
title: "Uniqueness of BP fixed point for the Potts model and applications to community detection"
doi: 10.48550/arXiv.2303.14688
url: https://arxiv.org/html/2303.14688v2
claim: "Lemma 20 and Appendix D.1 give local chi-square subadditivity for fully symmetric Potts channels; Appendix H states broader BP uniqueness and stability conjectures."
strata_touched:
  - D5/S3/Divergence/PottsLocalSubadditivity
license: citation-only
triage: anchor
---

# Local information combining for the Potts model

Y. Gu and Y. Polyanskiy, *Uniqueness of BP fixed point for the Potts model
and applications to community detection*, Proceedings of the Thirty Sixth
Annual Conference on Learning Theory, PMLR 195:837–884.

## Verified locator

Primary version: https://arxiv.org/html/2303.14688v2, Definitions 6 and 11,
Lemma 20, Appendix D.1 equations (137)–(166) and Lemma 35, Appendix D.2
equation (167), and Appendix H. DOI: 10.48550/arXiv.2303.14688.

[Proceedings](https://proceedings.mlr.press/v195/gu23a.html) ·
[Version 2](https://arxiv.org/html/2303.14688v2) ·
[DOI](https://doi.org/10.48550/arXiv.2303.14688).

## Finite-channel statement

The finite-channel setting uses a uniform input on q symbols and nonnegative
row-stochastic real matrices. Full symmetry is certified by an actual group
homomorphism from input permutations to output permutations preserving the
table under the simultaneous action. With output mass
`m_P(y) = q⁻¹ Σ_i P(i,y)`, write

`C₂(P) = q⁻¹ Σ_y (Σ_i P(i,y)²)/m_P(y) − 1`,

using real division, including `0/0 = 0`. The product channel has entries
`(P⋆Q)(i,(y,z)) = P(i,y)Q(i,z)`: its outputs are conditionally independent
given the same input.

Lemma 20, Appendix D.1, equations (137)–(166), establishes a local bound
with a constant depending only on q. The finite-output formalization permits
all output cardinalities, zero entries, zero-mass columns, redundant symbols
and trivial channels. For `q≥2`, `ε>0` and `C₂(P)≤ε`, it proves

`C₂(P⋆Q) ≤ (1 + (8q⁴+q) ε^(1/5)) (C₂(P)+C₂(Q))`.

The proof uses finite posterior mixtures, permutation cancellation of the
first variation, a rational remainder bound for small coordinate deviations,
and the good/bad split at posterior defect t² when the mean defect is at most
t⁵. Lemma 35 is the local fully symmetric-channel estimate. Appendix D.2,
equation (167), uses a uniform version of the local bound. The coefficient
`8q⁴+q` is an explicit sufficient constant; no optimality claim is made.

Appendix H supplies the research anchor:

> Above the KS threshold: We conjecture that BP uniqueness and BI always hold
> in this regime, and the unique non-trivial fixed point is globally stable.

This concerns belief-propagation dynamics and boundary irrelevance for the
Potts broadcast model above the Kesten–Stigum threshold. The finite local
combining estimate is a known ingredient, not a resolution of that broader
statement. The formalization does not include infinite output spaces,
convergence of iterated random-tree recursions, global high-signal stability,
or a stochastic-block-model transfer. It makes no claim of mathematical
novelty or exhaustive certification of the current literature status.
