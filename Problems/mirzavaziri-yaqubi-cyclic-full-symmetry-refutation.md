---
slug: mirzavaziri-yaqubi-cyclic-full-symmetry-refutation
bibkey: mirzavaziri2026cyclic
doi: 10.48550/arXiv.2609.28808
url: https://arxiv.org/abs/2609.28808v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result
---

# The Cyclic Latin Eulerian Numbers Are Not Fully Symmetric

## Problem

Madjid Mirzavaziri and Daniel Yaqubi, *Cyclic Latin Eulerian Numbers*, arXiv:2609.28808v1, Remark 3.9:

> Cyclically shifting π naturally explains an order-n cyclic symmetry for ⟨⟨n k⟩⟩_c. However, computations for n ≤ 5 (Table 1) reveal a
> surprising fact: ⟨⟨n k⟩⟩_c is actually invariant under the full symmetric group action on k … Identifying the hidden mechanism behind
> this full invariance remains an open problem.

Here `⟨⟨n k⟩⟩_c` counts permutations `π` whose row-reordered cyclic square `L_π` has column-ascent vector `k`.

## Motivation

The frozen theorem `D5/S3/Combinatorics/CyclicLatinEulerianRefutation.result` refutes the asserted invariance, and the module proves the
mechanism that actually governs the column-ascent vectors: one cyclic shift changes the ascent number only through the value that wraps
around, so the attained vectors take two adjacent values forming one cyclic interval. The failure holds for every `n ≥ 4`.

## Gap

Issue 10060 records the screen made before the work. The arXiv record has only v1; nothing under `Problems/`, `D5/` or `Library/`, and no
entry of the three screening records, concerns this paper. The paper's Table 1 lists one arrangement per multiset, which is why the
asymmetry was not visible there.

## Route

1. `shift_step`: for every `n ≥ 2`, the ascent number of column `c + 1` differs from that of column `c` by `[the wrapping value is in the
   first row] − [it is in the last row]`, where the wrapping value is the entry equal to `n − 1` in column `c`.
2. `no_three_changes`: three consecutive changes would need three distinct wrapping values located at the two end rows, which is impossible.
3. `not_fully_symmetric`: for every `n ≥ 4`, the permutation obtained from the identity by exchanging its last two values attains a vector
   with two adjacent high entries; exchanging two coordinates of that vector produces three consecutive changes, so the permuted vector is
   attained by no permutation while the original is attained.
4. `result`: the asserted invariance fails, already at `n = 4`.

## Falsifier

The statement would fail if the permuted vector were attained. It would not be the paper's statement if rows or columns of `L_π` were
indexed differently; the formal square is `L_π(i, c) = π(i) + c` over `Z/n`, the paper's row-reordered cyclic square, and direct enumeration with these definitions
reproduce every `n = 4` entry of the paper's Table 1.

## Evidence

Direct enumeration over `S_n` for `n = 4, …, 8`: every attained vector has two adjacent values with the larger forming one cyclic interval;
the sorted vector of each tested multiset is attained (2, 2, 16, 48, 384 times) while its alternating rearrangement is attained 0 times.

## Triage

`theorem`; Tier 1 open problem stated in a 2026 paper, preregistered in issue 10060 before the work. The computational use is `none`: the
central theorems hold for every `n`, and no declaration is a bounded enumeration, a checker, a numeric reduction or a certified instance.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources named above, for a paper three days old at screening; no worldwide priority claim is made.
