---
slug: oeis-a301976-grid-no-leaf-recurrence
bibkey: kagey2018a301976
doi: null
url: https://oeis.org/A301976
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence
---

# Barker's recurrence for no-leaf subgraphs of the 3 X n grid

## Problem

OEIS A301976, NAME (verbatim from `Library/Words/kagey2018a301976.md`):

> Number of no-leaf subgraphs of the 3 X n grid.

FORMULA (verbatim; attributed there to Colin Barker, Mar 30 2018):

> a(n) = 12*a(n-1) - 6*a(n-2) - 20*a(n-3) - 5*a(n-4) for n>4.

The literal object is the set of spanning edge-subgraphs of the `3 X n` grid
graph, with all `3n` vertices retained, in which every vertex has degree
different from one. Degree zero is allowed.

## Motivation

The order-four recurrence was recorded as a conjecture in 2018. Proving it
for every `n > 4` resolves the full unbounded scalar recurrence, rather than
only matching a finite prefix of the sequence.

## Gap

The bounded literature record dated 2026-09-13 in issue #7458 and its probe
report found that the OEIS history only restates the conjectures. Exact
identifier and phrase searches reported zero results on arXiv, OpenAlex,
Crossref, and MathOverflow. Math StackExchange question 2719054 is an
unanswered `2 X n` analogue. GitHub results were limited to OEIS mirrors,
sequence generators, and Kagey's Haskell enumerator. The two relevant files
in `peterkagey/OpenishProblems` pose only the general minimal-order question;
they do not prove this recurrence. This is bounded evidence, not an
exhaustive literature or priority claim.

## Route

The proof constructs a bijection between edge-subgraphs and paths of column
masks. The incoming and outgoing masks have eight states, and the two
vertical edges give four choices per column. Counting locally admissible
columns yields an eight-state transfer recurrence. A componentwise finite
calculation establishes the order-four identity
`P(M) * M * e0 = 0`, where
`P(X) = X^4 - 12*X^3 + 6*X^2 + 20*X + 5`. Multiplication by later powers of
`M`, followed by the edge-subgraph/path bijection, gives Barker's scalar
recurrence for every `n > 4`.

## Falsifier

One natural number `n > 4` for which
`a(n) != 12*a(n-1) - 6*a(n-2) - 20*a(n-3) - 5*a(n-4)` in the integers would
falsify the claim. A failure of the stated count to represent spanning
edge-subgraphs with no degree-one vertex would also invalidate the source
identification.

## Evidence

- Lean module: `D5/S1/Words/Patterns/GridNoLeafSubgraphRecurrence.lean`.
- Main theorem: `barker_a301976`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator independently brute-forced `n <= 4`, obtaining
  `1, 5, 43, 463`, and ran a separate transfer dynamic program through
  `n = 12`.
- The probe independently obtained the same values, checked the recurrence
  at every index `n = 5..12`, and checked the residue pattern at every index
  `n = 3..12`. These finite readings support but do not replace the theorem.

## Triage

`theorem`. The formal proof establishes Barker's complete order-four
recurrence for the literal A301976 counting function.

## ASSUMED-UNVERIFIED

No mathematical premise of the theorem is assumed. The claim that no prior
proof was found is limited to the dated literature surfaces listed in Gap;
arXiv coverage was reported by the probe and was not independently repeated
by this implementation. No exhaustive-search or first-publication claim is
made.
