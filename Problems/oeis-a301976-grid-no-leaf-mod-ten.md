---
slug: oeis-a301976-grid-no-leaf-mod-ten
bibkey: kagey2018a301976
doi: null
url: https://oeis.org/A301976
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
---

# Kagey's modulo-ten congruence for no-leaf grid subgraphs

## Problem

OEIS A301976, NAME (verbatim from `Library/Words/kagey2018a301976.md`):

> Number of no-leaf subgraphs of the 3 X n grid.

COMMENT (verbatim; attributed there to Peter Kagey):

> Conjecture: a(n) mod 10 = 3 for n > 2.

The literal object is the set of spanning edge-subgraphs of the `3 X n` grid
graph, with all `3n` vertices retained, in which every vertex has degree
different from one. Degree zero is allowed.

## Motivation

The congruence was recorded as a conjecture in 2018. The target is its full
unbounded range `n > 2`, not a finite residue table.

## Gap

The bounded literature record dated 2026-09-13 in issue #7458 and its probe
report found that the OEIS history only restates the conjectures. Exact
identifier and phrase searches reported zero results on arXiv, OpenAlex,
Crossref, and MathOverflow. Math StackExchange question 2719054 is an
unanswered `2 X n` analogue. GitHub results were limited to OEIS mirrors,
sequence generators, and Kagey's Haskell enumerator. The two relevant files
in `peterkagey/OpenishProblems` pose only the general minimal-order question;
they do not prove the modulo-ten statement. This is bounded evidence, not an
exhaustive literature or priority claim.

## Route

The companion theorem proves Barker's order-four recurrence for the same
literal counting function. Direct evaluation gives
`a(3), a(4), a(5), a(6) == 3 (mod 10)`. Strong induction applies the
recurrence at each later index. If its four preceding terms are all three
modulo ten, then
`12*3 - 6*3 - 20*3 - 5*3 == 3 (mod 10)`, completing the induction.

## Falsifier

One natural number `n > 2` with `a(n) mod 10 != 3` would falsify the claim.
A failure of the stated count to represent spanning edge-subgraphs with no
degree-one vertex would also invalidate the source identification.

## Evidence

- Lean module: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.lean`.
- Main theorem: `kagey_a301976_mod10`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator independently brute-forced `n <= 4`, obtaining
  `1, 5, 43, 463`, and ran a separate transfer dynamic program through
  `n = 12`.
- The probe independently obtained the same values, checked Barker's
  recurrence at every index `n = 5..12`, and checked this residue pattern at
  every index `n = 3..12`. These finite readings support but do not replace
  the theorem.

## Triage

`theorem`. The formal proof establishes Kagey's complete modulo-ten
congruence for the literal A301976 counting function.

## ASSUMED-UNVERIFIED

No mathematical premise of the theorem is assumed. The claim that no prior
proof was found is limited to the dated literature surfaces listed in Gap;
arXiv coverage was reported by the probe and was not independently repeated
by this implementation. No exhaustive-search or first-publication claim is
made.
