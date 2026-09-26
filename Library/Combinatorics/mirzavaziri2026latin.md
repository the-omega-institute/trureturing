---
bibkey: mirzavaziri2026latin
authors: Madjid Mirzavaziri, Daniel Yaqubi
year: 2026
title: "Latin Eulerian Numbers"
doi: 10.48550/arXiv.2609.25100
url: https://arxiv.org/abs/2609.25100v1
claim: "every multiple of n strictly between n and (n − 1)^2 − 1 is attained by some Latin square … verified for n ≤ 11 but open in general"
strata_touched:
  - D5/S3/Combinatorics/LatinEulerianMultiples
license: citation-only
triage: anchor
---

# Mirzavaziri and Yaqubi, Latin Eulerian numbers

The paper refines the Eulerian numbers to Latin squares by counting, for each column, the ascents read from top to bottom.
Its total ascent statistic Σ(L) satisfies n − 1 ≤ Σ(L) ≤ (n − 1)², with n and (n − 1)² − 1 unattainable, and the row-reordered
cyclic squares attain every interior value that is not a multiple of n.

## Verified locator

DOI: 10.48550/arXiv.2609.25100

URL: https://arxiv.org/abs/2609.25100v1

The arXiv record shows only v1 (19 September 2026).

- Locator: Definition 2.3, `k_i(L) = asc(c_i(L))` for the i-th column read top to bottom; Definition 4.1, `Σ(L) = Σ_i k_i(L)`.
- Locator: Proposition 4.6, the row-reordered cyclic squares never attain a multiple of n; Corollary 4.7, the interior multiples are
  `2n, 3n, …, (n − 3)n`.
- Locator: Remark 4.16, "Precisely two things remain: (i) that every multiple of n strictly between n and (n − 1)^2 − 1 is attained
  by some Latin square … verified for n ≤ 11 but open in general; (ii) unimodality of (T_n(m)) …".

## Reading of the statement

Since `(n − 1)² − 1 = n(n − 2)`, part (i) asks, for every `n ≥ 5` and `2 ≤ k ≤ n − 3`, for an order-`n` Latin square with
`Σ(L) = kn`. Part (ii), the unimodality of the distribution `T_n`, is a separate statement.

## Scope of the recorded answer

Part (i) holds. For a permutation `p` of `0, …, n − 1`, the square `L_p(i, c) = τ((p_i + c) mod n)`, with `τ` exchanging the
symbols 0 and 1, satisfies `Σ(L_p) = n·a(p) + p_0 − p_{n−1} − u(p) + v(p)`, where `a` counts ordinary ascents of `p` and `u`, `v` count
cyclic differences 1 and n − 1. Explicit permutations reach every `kn` with `2 ≤ k ≤ ⌊(n − 2)/2⌋` and the odd midpoint; reversing
the rows, which sends `Σ` to `n(n − 1) − Σ`, covers the rest. Part (ii) is not addressed.

## Bounded prior-resolution evidence

Read on 2026-09-26: the arXiv record (v1 only); the only other paper titled with Latin Eulerian numbers is the authors'
arXiv:2609.28808v1, which does not treat part (i); google-deepmind formal-conjectures and conjectures.io have no entry. This is a
bounded negative finding.
