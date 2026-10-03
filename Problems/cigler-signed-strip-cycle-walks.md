---
slug: cigler-signed-strip-cycle-walks
bibkey: cigler2026narayana
doi: 10.48550/arXiv.2608.03363
url: https://arxiv.org/abs/2608.03363v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result
---

# Signed Dyck Paths in the Strip of Height 4k − 2 Count Walks on the 4k-Cycle

## Problem

Johann Cigler, *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana
polynomials for q=-1*, arXiv:2608.03363v2, Section 3, Conjecture 1, equation (74) (absent from v1): for k ≥ 1, with
U_k the adjacency matrix of the cycle on 4k vertices,

c_{2n+1}^{(4k−2)} = U_k^{2n+1}(0, 1),  c_{2n+2}^{(4k−2)} = U_k^{2n+2}(0, 0) = 2 c_{2n+1}^{(4k−2)}.

Here c_r^{(H)} = c_r^{(H)}(1) is the weighted count of Dyck paths of semilength r in the strip 0 ≤ y ≤ H, a down-step to
height j having weight (−1)^{⌊j/2⌋}, that is the q = −1 weights (1, t, −1, −t, …) at t = 1.

## Motivation

The theorem `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result` establishes the three equalities for every
k ≥ 1 and n ≥ 0.

## Gap

Pre-registration issue 12579 records the literature screen: the arXiv record lists the statement as a conjecture in
v2; OEIS A007582 and A085282 record the walk interpretation for the 8-cycle and the 12-cycle only, and web and
GitHub searches found no proof for general k. This is a bounded negative finding.

## Route

1. Pairing the steps of a Dyck path in the strip of height 4k − 2 gives a weight-preserving bijection with
   two-coloured Motzkin paths in the strip of height 2k − 1 (the bijection of `CiglerStripExpansionPairing`).
2. With these weights the two flat colours at an interior height have opposite signs and cancel; paired up and down
   steps have weight 1, and the single admissible flat step at height 0 and at height 2k − 1 has weight 1.
3. Hence c_r^{(4k−2)} counts walks of length r on the path with 2k vertices carrying a loop at each end, from the
   first vertex back to it.
4. Folding the 4k-cycle by the reflection j ↦ 4k − 1 − j maps walks from 0 onto walks on that looped path with unique
   lifts, so c_r^{(4k−2)} = U_k^r(0, 0) + U_k^r(0, 4k − 1); bipartiteness and the reflection symmetry give the three
   equalities.

## Falsifier

The statement would fail if a boundary flat step had weight −1, or if a quotient walk had two lifts.

## Evidence

An independent referee implementation checked the three equalities and every intermediate lemma; the original proof's
checks cover k ≤ 20 and n ≤ 50.

## Triage

`theorem`; the statement is Conjecture 1 of arXiv:2608.03363v2 and is quantified over every k ≥ 1 and n ≥ 0.

- Proved (formalized): the three equalities of (74) for every k ≥ 1 and n ≥ 0.
- Proved (formalized): under the weights (1, 1, −1, −1, …) the strip-(4k − 2) signed path sum equals the number of
  closed walks at an end of the 2k-vertex path with loops at both ends.
- Open: the analogue for strip heights not of the form 4k − 2, which the source does not state.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, OEIS, web and GitHub searches and the repository checks
recorded above.
