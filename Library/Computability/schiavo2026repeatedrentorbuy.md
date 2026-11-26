---
bibkey: schiavo2026repeatedrentorbuy
authors: Vasco Schiavo
year: 2026
title: "A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy"
doi: null
url: https://arxiv.org/abs/2611.06955v1
claim: "Section 5.B's third question asks whether a single rule can lose at most 2K on two runs and be c-competitive for some constant c."
strata_touched:
  - D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy
  - D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive
  - D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy
  - D5/S3/Analytic/Polynomial/OrderedCrossingGap
license: citation-only
triage: anchor
---

# A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy

Vasco Schiavo, arXiv:2611.06955v1 [cs.DS], 3 November 2026. The cited v1 PDF has SHA-256
`983611ccff31a84944219b759d5a244772fefc8b7574039064419a47bfc71cb5`.

Section 5.B, PDF page 15, third question:

> Can a rule lose at most 2K on two runs and also be c-competitive for some constant c?

Definitions 2 and 3, PDF pages 3–4, specify a session of $T$ calls and $T-1$ nonnegative real increments. A run is a maximal constant consecutive block, and the number of runs is zero at $T=1$. A reset has fixed price $K>0$. With reset bit $r_t$ and history $h_t$, the source bills $h_t+Kr_t$, starts at $h_1=0$, and updates $h_{t+1}=(1-r_t)h_t+a_t$ for $t<T$. The rent is charged on each reset call and on the final call. The comparator is an arbitrary schedule on the same increments, so minimizing over the finite schedule space gives the offline cost. [Primary source, §2](https://arxiv.org/pdf/2611.06955v1#page=3)

Proposition 6 and Lemmas 7–8 give the fair cost at a positive constant rate and the associated one-call potential relations. Lemma 14 gives the comparator potential's monotonicity in the rate. Lemma 17 treats the ordinary threshold rule at an increase, including the ordered polynomial expression on pages 14–15. Theorem 16 establishes the two-run lower bound. Theorem 18 gives the additive guarantee for the drop-aware rule, which the paper shows lacks a universal competitive factor. [Primary source, §5](https://arxiv.org/pdf/2611.06955v1#page=12)

## Verified locator

- URL: https://arxiv.org/abs/2611.06955v1 (v1, 2026-11-03). The definitions appear on PDF pages 3–4. The third question of §5.B appears on PDF page 15.
