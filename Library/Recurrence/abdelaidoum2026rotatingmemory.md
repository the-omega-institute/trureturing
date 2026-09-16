---
bibkey: abdelaidoum2026rotatingmemory
authors: Walid Abdelaidoum; El-Mehdi Mehiri; Hacene Belbachir
year: 2026
title: Rotating-Memory Fibonacci Numbers and Periodic Tilings
doi: null
url: https://arxiv.org/html/2609.12569v1
claim: "Definition 1 defines R_0^(k)=0, R_1^(k)=1, and R_n^(k) as the sum of the preceding 2+(n mod k) terms; Theorem 1 states R_(n+k)^(k)=3*2^(k-2)*R_n^(k) for k>=2 and n>=k."
strata_touched:
  - D5/S1/Recurrence/Periodic/RotatingMemoryFibonacciPeriodCollapse
license: CC-BY-4.0
triage: anchor
---

# Rotating-Memory Fibonacci Numbers and Periodic Tilings

The paper introduces the rotating-memory Fibonacci sequence. It declares that
negative-index terms are zero and states Definition 1 as

> Let k >= 1. The Rotating-memory Fibonacci sequence of period k is defined by
> R_0^(k) = 0, R_1^(k) = 1, and, for every n >= 2,
> R_n^(k) = sum from j = 1 through 2 + (n mod k) of R_(n-j)^(k).

Theorem 1 states

> Let k >= 2. Then, for every n >= k,
> R_(n+k)^(k) = 3 * 2^(k-2) * R_n^(k).

The Lean definition uses natural subtraction to implement the stipulated zero
values at negative indices. The formal period-collapse theorem retains the
source hypotheses and conclusion.

## Scope boundary

The paper proves the one-period scaling formula and later gives geometric
residue-class formulas and valuation consequences. It does not state that the
k by k tail Hankel matrix with entries R_(k+i+j) has nonzero determinant or
full rank. That arbitrary-dimension nonsingularity theorem is a
repository-derived consequence of the within-block powers, period collapse,
and an explicit elimination of the resulting threshold matrix. No claim from
the tiling section is used.

Repository and pinned-Mathlib searches found no exact formalization. The
completed authenticated GitHub code searches for `rotating memory fibonacci`,
`period_collapse rotatingMemory`, `RotatingMemoryFibonacci`,
`rotatingMemory language:Lean`, and `period_collapse language:Lean` found no
Lean implementation; the search for `2609.12569` returned metadata and
non-Lean results only.

## Verified locator

- Versioned paper: https://arxiv.org/html/2609.12569v1
- arXiv identifier: 2609.12569v1
- First submitted: 2026-09-11T08:12:35Z
- Source locations: Definition 1 in Section 2 and Theorem 1 in Section 3
- License: https://creativecommons.org/licenses/by/4.0/
