---
slug: oeis-a326244-noncrossing-nonnesting-graph-recurrence
bibkey: barker2019a326244
doi: null
url: https://oeis.org/A326244
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence
---

# Barker's recurrence for crossing- and nesting-free labeled graphs

## Problem

OEIS A326244, NAME:

> Number of labeled n-vertex simple graphs without crossing or nesting edges.

COMMENTS:

> Two edges {a,b}, {c,d} are crossing if a < c < b < d or c < a < d < b, and nesting if a < c < d < b or c < a < b < d.

FORMULA:

> Conjectures from _Colin Barker_, Jun 28 2019: (Start)
>
> G.f.: (1 - x)*(1 - 4*x) / (1 - 6*x + 8*x^2 - 4*x^3).
>
> a(n) = 6*a(n-1) - 8*a(n-2) + 4*a(n-3) for n>2.
>
> (End)

The entry line is `_Gus Wiseman_, Jun 20 2019`. The generating-function line
is the same third-order recurrence together with initial values `1, 1, 2`; no
separate generating-function identity is claimed here.

## Motivation

This 2019 OEIS conjecture asks for an exact unbounded recurrence for a literal
class of labeled simple graphs. Proving it resolves the stated open problem
without replacing the graphs by an auxiliary encoding in the public theorem.

## Gap

The 2026-09-13 search recorded on issue #7437 found zero relevant proof hits
on Crossref and OpenAlex. A GitHub claim-level search also found zero proofs;
exact-token results were sequence mirrors or programs that assumed the
recurrence. Marberg (2013) and de Mier (2006) study related crossing and
nesting classes, not this intersection count. The arXiv search is
`ASSUMED-UNVERIFIED` because the probe ended before preserving a complete
search receipt. This bounded search does not establish publication priority.

## Route

For an avoiding graph `G`, let `A(G)` be the vertices `c` such that every edge
whose right endpoint is greater than `c` is incident with `c`. Removing the
greatest vertex gives a bijection

`avoiding(n+1) ≃ Σ_G P(A(G))`.

The private restriction and gluing maps implement the two directions and
prove that the avoiding condition is preserved. If the chosen subset `S` has
size `r`, the allowed-set size after gluing is `r+1` when `S` is empty, `2`
when `S` is a singleton, and `1` when `S` has at least two elements. The proof
then uses the moments `X`, `Y`, and `Z`, with

`X_(n+1) = Z_n`,

`Y_(n+1) = 2*Y_n + Z_n`,

`Z_(n+1) + 2*X_n = 2*Y_n + 4*Z_n`.

Eliminating `Y` and `Z` yields the third-order recurrence for the literal
count `a`. All state machinery is private; only the source definitions and
the final recurrence form the public surface.

## Falsifier

One index `n > 2` for which the literal graph count differs from
`6*a(n-1) - 8*a(n-2) + 4*a(n-3)` would refute the result.

## Evidence

- Lean module: `D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.lean`.
- Main theorem: `barker_a326244`.
- Public definitions: `Crossing`, `Nesting`, `IsAvoiding`, and `a`.
- The theorem's axiom closure is std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator independently counted conflict-graph independent sets for
  `n = 0..7`, obtaining `1, 1, 2, 8, 36, 160, 704, 3088`, exactly the values
  produced by the recurrence from initial values `1, 1, 2`.
- The search seat exhaustively checked all `2,131,020` graphs through `n = 7`
  and reported zero mismatches.

The finite computations support the statement; the Lean proof establishes
the recurrence for every natural `n > 2`.

## Triage

`theorem`. The formal result proves Barker's recurrence for the exact labeled
graph class stated by OEIS A326244.

## ASSUMED-UNVERIFIED

The arXiv search was not independently completed by this seat. The source
quotation, attribution, search-surface readings, related-literature scope,
and supporting finite enumerations are external evidence rather than
kernel-checked facts. No claim of exhaustive literature coverage, priority,
or a separately formalized generating-function identity is made.
