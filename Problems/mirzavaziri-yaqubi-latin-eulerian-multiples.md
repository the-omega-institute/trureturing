---
slug: mirzavaziri-yaqubi-latin-eulerian-multiples
bibkey: mirzavaziri2026latin
doi: 10.48550/arXiv.2609.25100
url: https://arxiv.org/abs/2609.25100v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/LatinEulerianMultiples.result
---

# Every Interior Multiple of n Is a Latin-Square Ascent Total

## Problem

Madjid Mirzavaziri and Daniel Yaqubi, *Latin Eulerian Numbers*, arXiv:2609.25100v1, Remark 4.16:

> Precisely two things remain: (i) that every multiple of n strictly between n and (n − 1)^2 − 1 is attained by some Latin square
> which Proposition 4.14 reduces to an explicit, checkable question about the function F, verified for n ≤ 11 but open in general;
> (ii) unimodality of (T_n(m)) …

Here `Σ(L)` is the sum over the columns of an order-`n` Latin square of the number of ascents read from top to bottom. Part (i)
asks, for every `n ≥ 5` and `2 ≤ k ≤ n − 3`, for an order-`n` Latin square with `Σ(L) = kn`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/LatinEulerianMultiples.result` proves part (i). Together with the paper's results it shows
that the set of attained values of `Σ` is exactly `[n − 1, (n − 1)²]` with the two values `n` and `(n − 1)² − 1` removed.

## Gap

Issue 9995 records the screen made before the work. The arXiv record has only v1; the authors' companion paper arXiv:2609.28808v1
does not treat part (i); google-deepmind/formal-conjectures and conjectures.io have no entry. Nothing under `Problems/`, `D5/` or
`Library/`, and no entry of the three screening records, concerns this paper.

## Route

1. For a permutation `p` of `0, …, n − 1` let `L_p(i, c) = τ((p_i + c) mod n)`, where `τ` exchanges the symbols 0 and 1. It is a
   Latin square.
2. For adjacent rows with cyclic difference `δ`, exactly `n − δ` columns ascend before `τ` is applied; `τ` changes only the directed
   pairs `(0, 1)` and `(1, 0)`, which occur once when `δ = 1` and once when `δ = n − 1`. Summing and telescoping gives
   `Σ(L_p) = n·a(p) + p_0 − p_{n−1} − u(p) + v(p)`, where `a` counts ordinary ascents of `p` and `u`, `v` count cyclic differences
   1 and `n − 1`.
3. Three explicit permutations give `a = k` and `p_0 − p_{n−1} = u − v`: one for `k = 2`, a four-block family for
   `3 ≤ k ≤ ⌊(n − 2)/2⌋`, and one for the odd midpoint `k = (n − 1)/2`.
4. Reversing the rows exchanges ascents and descents in every adjacent pair, so `Σ` becomes `n(n − 1) − Σ`; this covers
   `k' = n − 1 − k` for the remaining targets.

## Falsifier

The statement would fail if some interior multiple of `n` were not attained. It would not be the paper's statement if ascents were
counted along rows or cyclically; the formal definitions count ascents in each column from top to bottom, exactly as Definition 2.3.

## Evidence

The construction was checked directly for every `5 ≤ n ≤ 60` and every `2 ≤ k ≤ n − 3` (1,596 cases): each square is Latin and its
column-ascent total equals `kn`.

## Triage

`theorem`; Tier 1 open subproblem stated in a 2026 paper, preregistered in issue 9995 before the work. The computational use is
`none`: the delivered statement is universally quantified over every `n ≥ 5` and `2 ≤ k ≤ n − 3`, and no declaration is a bounded
enumeration, a checker, a numeric reduction or a certified instance.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above; the paper was one week old when screened, so no worldwide priority
claim is made. Part (ii) of Remark 4.16, the unimodality of `T_n`, is not addressed.
