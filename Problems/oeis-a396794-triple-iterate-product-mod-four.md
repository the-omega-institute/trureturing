---
slug: oeis-a396794-triple-iterate-product-mod-four
bibkey: hanna2026a396794
doi: null
url: https://oeis.org/A396794
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/TripleIterateProductModFour
---

# Divisibility of the A396794 coefficients

## Problem

OEIS A396794, Paul D. Hanna, Jun 07 2026. The following exact NAME and
COMMENT quotations are recorded in `Library/Arith/hanna2026a396794.md`.

NAME:

> G.f. A(x) satisfies A(x) * A(A(A(x))) = x^2 + 16*x^3.

COMMENT:

> Conjecture: a(n) == 0 (mod 4) for n > 1.

The formal target uses the normalized integer series with constant coefficient
zero and degree-one coefficient one; `a(n)` is its degree-n coefficient.

## Motivation

This is the first-tier recent OEIS conjecture selected in the implementation
brief. The target is the assertion for every index greater than one.
KPI = open problems resolved.

## Gap

The search seat reported no proof found in its 2026-09-08 reading of the OEIS
entry and revision history, and identifier searches on arXiv, MathOverflow,
and GitHub. This Stage-B seat had no network and did not repeat those searches.
The report is limited to that searched scope, not an exhaustive literature claim.

## Route

Coefficient lifting constructs a normalized integer solution. At each degree,
the mod-16 error identity makes division by four exact; the stabilized
coefficients satisfy the full functional equation. Coefficient perturbation
then proves uniqueness among normalized integer solutions (`generating_unique`).

For divisibility, strong induction truncates the solution below degree n.
The earlier coefficients make this prefix `x + 4B`. Modulo 16, its jth
compositional iterate is `x + 4jB`, so its product with its third iterate is
congruent to `x^2`. The private `product_top` identity says that the
degree-(n+1) coefficient of `A * A^{\circ 3}` changes by exactly four times
the degree-n perturbation when normalized series agree below n. Comparing
the prefix with the solution to the actual functional equation gives
`16 | 4c`, hence `4 | c`, with `c = a(n)`.

The generality-I module binds the frozen
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence` for `iterate`.
Freeze prerequisite statement_id, read from its state file:
`sha256:4063c4732963765b6b16b5dda51775b4d179cfc3a203c91ed15e3ebffb0467e7`.
The imported `fixed_unique` concerns a different equation; uniqueness here
uses the new coefficient-perturbation argument.

## Falsifier

An index `n > 1` with `4` not dividing `a(n)` for the normalized solution
would contradict the assertion. The orchestrator's exact coefficient check
is supporting evidence only; no finite bound replaces the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Invariants/TripleIterateProductModFour.lean`.
- Main public theorem: `hanna_conjecture`.
- Companions: `generating_equation` (equation and normalization) and
  `generating_unique` (uniqueness); `generatingSeries` and `a` define the objects.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for all three
  public theorems, as reported by the implementation seat's `#print axioms`.
- The implementation seat reported single-file Lean compilation with exit 0;
  the orchestrator reported separate build/report verification. This seat
  did not rerun those checks.

## Triage

`theorem`. The formal proof closes the universal divisibility assertion for
the normalized integer solution, with existence and uniqueness companions.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and copied from the Library
note. The search seat, not this seat, read the OEIS entry and revision history
on 2026-09-08. The reported literature scope was identifier search on arXiv,
MathOverflow, and GitHub, with no proof found in that scope. This seat had no
network and did not independently verify those external readings, the exact
numerical check, or exhaustive literature coverage. First-publication priority
and source-to-Lean identification are not kernel-checked facts.
