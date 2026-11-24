---
slug: popov-2026-direct-urn-shift
bibkey: popov2026mstirling
doi: 10.48550/arXiv.2608.12011
url: https://arxiv.org/abs/2608.12011v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/PopovDirectUrnShift.shift_7_2
---

# A direct urn bijection for Popov's shift identity

## Problem

> Problem 9.1. Find a direct bijective proof of the shift identity (7.2) in the urn model of Theorem 7.13: the right-hand side suggests distinguishing, in a placement of $n + m$ marbles, the $j$ marbles that avoid the “last” urn, with the factor $m^{n-j}$ recording an $m$-fold choice for each of the remaining marbles. Such a proof would make the “pairing effect” heuristic of Section 5 precise.

Vencislav Popov, *m-Bell and m-Stirling numbers*, §9.3. The quotation uses Markdown math for the original symbols. [arXiv:2608.12011v1, p. 29](https://arxiv.org/pdf/2608.12011v1#page=29) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

## Motivation

The factor $m^{n-j}$ should count actual choices of slots. A chronological inverse must also recover which marbles made those choices.

## Gap

Theorem 7.3 already proves the numerical identity by induction. The direct map resolves Problem 9.1 in the model of Theorems 5.1 and 7.13. [Prior algebraic proof](https://arxiv.org/pdf/2608.12011v1#page=22) · [Problem and scope](https://github.com/the-omega-institute/trureturing/issues/33770)

## Route

For $m\geq 1$, use chronological assignments of marble positions to urn and slot addresses, modulo arbitrary urn permutations and per-urn slot permutations. Order the urns and slots by first use. A prefix with $p$ distinct pairs has exactly ranks $[0,p)$ and permits the fresh rank $p$ or an old rank below $m\lfloor p/m\rfloor$.

The first $m$ placements fill the first urn in every orbit. In the tail, choose the subset $J$ that avoids that urn. Keep those placements in increasing order and shift their ranks down by $m$. Each complementary position keeps its first-urn color in $\mathrm{Fin}(m)$. Reinsertion puts back the forced prefix, shifts the residual ranks up by $m$, and interleaves the recorded colors and residual placements. At each retained move the occupied count is $m$ plus the residual count. A move to a first-urn color remains legal while a later urn is incomplete.

## Falsifier

A legal raw history outside the normalization image, unequal raw orbits with equal normalized words, or a source or payload on which either composite fails would contradict the corresponding map law. A discrepancy in the number of distinct occupied pairs or in the negative and zero columns would contradict the counting statement.

## Evidence

- `PopovUrnShift.normalize_eq_iff`, `normalize_replay` and `replay_normalize_orbit` identify the actual relabeling quotient with canonical words in any ambient of at least the length of the history.
- `PopovUrnShift.reinsert_delete` and `delete_reinsert` are the pointwise inverse laws. The raw retained-address theorem identifies the used set outside the first urn, and `retained_raw_count` proves that exactly $m$ distinct pairs are removed.
- `signedFirstUrnEquiv` connects the same source quotient to `SignedPayload` at the integer difference $k-m$. If $k\geq m$, the unique natural count $r$ with $r=k-m$ carries the original subset, colors, and residual orbit through `firstUrnEquiv`. If $k<m$, `below_first_urn` and `signed_payload_empty` supply the two empty carriers. The second witness excludes a natural count whose integer image is negative.
- `card_urn_eq_stirling` identifies the actual quotient count using the empty history and the last move. There is one history at $(t,k)=(0,0)$ and no positive-length history with $k=0$. At a positive column $k$ there are $m\lfloor k/m\rfloor$ old-slot choices and one fresh choice from column $k-1$.
- `shift_7_2` takes cardinalities of the bijection and groups subsets by size. The signed count vanishes at negative columns.

## Triage

### What the settlement shows

- **Proved.** For every positive capacity and all natural tail sizes and column indices, the chronological bijection gives (7.2). At column $k=m+r$ its residual has exactly $r$ used pairs. Below $m$ both the source and the signed payload are empty. [Lean result](../D5/S1/Recurrence/Invariants/PopovDirectUrnShift.lean)
- **Proved.** Capacity one gives the usual restricted-growth rule, with the first marble's block distinguished and a unique complement color. An empty tail gives the single forced-prefix orbit in column $m$ and the empty residual, with all other columns empty. The partial later urn case is permitted by the local rule for the full first urn. [Lean boundaries](../D5/S1/Recurrence/Invariants/PopovDirectUrnShift.lean)
- The direct proof supplies the combinatorial interpretation requested in Problem 9.1. Theorem 7.3 and its numerical consequences already follow from the recurrence. The other problems in §9.3 concern distinct statements. [Popov, §9.3](https://arxiv.org/pdf/2608.12011v1#page=29)

## ASSUMED-UNVERIFIED

The bounded literature search found no exact direct proof beyond the classical case. Coverage of unindexed work and publication priority remain unverified. [Issue #33770](https://github.com/the-omega-institute/trureturing/issues/33770)
