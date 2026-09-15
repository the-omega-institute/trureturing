---
slug: oeis-a192023-comb-wiener-determinant-refutation
bibkey: kimberling2012a192023
doi: null
url: https://oeis.org/A192023
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation
---

# Refutation of the A192023 comb-Wiener determinant-count conjecture

## Problem

OEIS A192023, NAME (verbatim):

> The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes. The Wiener index of a connected graph is the sum of the distances between all unordered pairs of vertices in the graph.

FORMULA (verbatim):

> a(n) = n*(2*n^2 + 6*n - 5)/3.

COMMENT (verbatim; Clark Kimberling, Mar 31 2012):

> Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in {1,2,...,n} and determinant 2n. - _Clark Kimberling_, Mar 31 2012

Here `A192023(n-2)` means the Wiener index of the comb on
`2(n-2)` vertices, as specified by the NAME, rather than an assumed
use of the closed formula.

## Motivation

This first-tier OEIS conjecture was printed in 2012 and remains unchanged in
the live revision recorded by preregistration issue #7441. A certified
counterexample resolves the literal universal comment while leaving the
sequence definition and its cubic formula unchanged.

## Gap

Preregistration issue #7441 and its probe report record searches dated
September 13, 2026. OpenAlex returned only the 2022 paper *Wiener Index of
Some Brooms*, which proves the FORMULA and does not address the matrix
comment. Exact identifier searches returned 0 results on MathOverflow and
0 on arXiv. GitHub results were sequence generators and unchanged copies of
the OEIS comment; the probe recorded 333 broad hits and 2 exact
`A192023`-with-`determinant` hits, neither a proof,
refutation, or correction. No resolution was found in those bounded surfaces.
This does not assert exhaustive literature coverage or publication priority.

## Route

Take `n = 3`. The comb indexed by `n-2 = 1` is a single
edge on two vertices, so its only unordered pair has distance one and
`A192023(1) = 1`.

For a matrix `[[a,b],[c,d]]` with every entry in `{1,2,3}`,
the determinant condition is `ad-bc = 6`. Since `bc >= 1`,
it forces `ad >= 7`; because `a,d <= 3`, this gives
`a = d = 3`. Then `bc = 3`, so the only possibilities are
`(b,c) = (1,3)` and `(3,1)`. Thus exactly
`[[3,1],[3,3]]` and `[[3,3],[1,3]]` are counted, and the
matrix count is two. Since `1 != 2`, the literal comment is false
at its first allowed input.

## Falsifier

The refutation would fail if the comb on two vertices were not a single edge,
if its unique unordered-pair distance were not one, if a third matrix in
`{1,2,3}^{2 x 2}` had determinant six, or if either displayed
matrix failed the determinant condition. The Lean theorem computes the graph
distance and exhaustively classifies all 81 matrices.

## Evidence

- Lean module:
  `D5/S0/Certificates/KimberlingCombWienerDeterminantRefutation.lean`.
- Main theorem: `result : ¬ claim`, with exactly the std3 axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Public definitions: `comb`, `wienerIndex`,
  `matrixCount`, and `claim`.
- The orchestrator's independent BFS gives Wiener indices for comb sizes
  `m = 1..6` as `1, 10, 31, 68, 125, 206`, equal to the
  FORMULA values.
- The orchestrator's independent matrix counts for `n = 3..12` are
  `2, 9, 16, 33, 42, 69, 92, 123, 130, 228`, while
  `A192023(n-2)` is
  `1, 10, 31, 68, 125, 206, 315, 456, 633, 850`.
- The probe independently extended the BFS through `m = 10`,
  reproduced the matrix counts through `n = 12`, and found the two
  row-major witnesses `(3,1,3,3)` and `(3,3,1,3)` among
  all 81 matrices at `n = 3`.

The two checked sequences disagree at every `n = 3,...,12`. The
recorded hypothesis is that the comment was misplaced, but this bounded
pattern is not a proof of its intended location or wording. The formal result
refutes only the literal printed comment, and no corrected statement is
claimed.

## Triage

`theorem`. The certified instance at `n = 3` refutes the
universal comment. It makes no claim about equality or inequality at
unverified inputs and asserts no corrected indexing.

## ASSUMED-UNVERIFIED

The external search counts, the unchanged live-revision observation, the
orchestrator's bounded numerical tables, and the probe's `m = 1..10`
/ `n = 3..12` computations are supplied readings from issue #7441
and were not recomputed by this implementation seat. The "misplaced comment"
explanation is a hypothesis, not a result. No exhaustive literature,
intended-statement, or first-publication claim follows.
