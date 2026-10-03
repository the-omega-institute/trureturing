---
slug: cigler-narayana-strip-expansion
bibkey: cigler2026narayana
doi: 10.48550/arXiv.2608.03363
url: https://arxiv.org/abs/2608.03363v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result
---

# Expansions of Narayana-Weighted Dyck Paths in an Even Strip

## Problem

Johann Cigler, *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana
polynomials for q=-1*, arXiv:2608.03363v2, Section 4, Conjecture 3 (Conjecture 2 in v1): for m ≥ 1 and n ≥ 0,

C_{n+1}^{(2m)}(t) = Σ_{j=0}^{⌊n/2⌋} C_j^{(m−1)} binom(n, 2j) t^j (1 + t)^{n−2j},

c_{n+1}^{(2m)}(t) = Σ_{j=0}^{⌊n/2⌋} (−1)^j C_j^{(m−1)} binom(⌊n/2⌋, j) t^j (1 + t)^{n−2j}.

Here C_n^{(h)}(t) and c_n^{(h)}(t) are the weighted counts of Dyck paths of semilength n in the strip
0 ≤ y ≤ h, a down-step to height k having weight τ_k with τ = (1, t, 1, t, …) and τ = (1, t, −1, −t, …)
respectively, and C_j^{(m−1)} is the number of Dyck paths of semilength j in the strip of height m − 1.

## Motivation

The theorem `D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansion.result` establishes both identities for every
m ≥ 1 and n ≥ 0 in ℤ[t].

## Gap

Pre-registration issue 12523 records the literature screen: the arXiv record has v1 and v2, both listing the
statement as a conjecture, and searches of the arXiv identifier on the web and on GitHub returned no proof outside
this repository. This is a bounded negative finding.

## Route

1. Remove the first and last steps of a path of semilength n + 1 in the strip of height 2m and pair the remaining
   2n steps. Sampling at odd times with coarse height a turns UU and DD into up and down steps and UD, DU into two
   kinds of flat steps; this is a weight-preserving bijection with weighted Motzkin paths of length n in the strip
   of height m − 1, the steps DU at coarse height 0 and UD at coarse height m − 1 included.
2. Deleting the flat steps leaves a Dyck skeleton of semilength j, counted by C_j^{(m−1)}; the flat steps fill the
   2j + 1 gaps of the skeleton with colours.
3. With Narayana weights a skeleton with a fixed gap filling, summed over the colours of its flat steps, has weight
   t^j (1 + t)^{n−2j}, and the gap fillings are counted by binom(n, 2j).
4. With the q = −1 weights the sign of a flat step depends on the parity of the index of its gap. An involution
   that moves a block of flat steps across one skeleton step into the neighbouring gap keeps the skeleton and the
   colours and reverses the sign of every non-fixed filling; the fixed gap tuples are counted by binom(⌊n/2⌋, j)
   and carry the sign (−1)^j.

## Falsifier

The statement would fail if the pairing missed a boundary move at coarse height 0 or m − 1, or if the involution
failed to preserve weight or to reverse sign outside its fixed points.

## Evidence

An independent referee implementation checked both identities and every intermediate bijection exhaustively for
m ≤ 6 and n ≤ 16, and both identities coefficientwise by a step-by-step polynomial recursion for m ≤ 10 and n ≤ 40.

## Triage

`theorem`; the statement is Conjecture 3 of arXiv:2608.03363v2 and is quantified over every m ≥ 1 and n ≥ 0.

- Proved (formalized): both expansion identities for every m ≥ 1 and n ≥ 0.
- Proved (formalized): the pairing of steps is a weight-preserving bijection between strip-2m Dyck paths of
  semilength n + 1 and weighted Motzkin paths of length n in the strip of height m − 1; the expansions are the
  skeleton decomposition of these Motzkin paths.
- Open: an analogous closed expansion for odd heights 2m + 1, which the source does not state.
- Open: Conjecture 2 of the same section (the product formula for heights 4m and 4m + 1) is a separate statement
  and is not implied by these expansions.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv record, web and GitHub searches and the repository checks recorded
above.
