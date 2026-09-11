---
slug: oeis-a378576-shifted-iterate-fixed-point-mod-five
bibkey: hanna2024a378576
doi: null
url: https://oeis.org/A378576
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence
---

# The A378576 shifted-iterate fixed-point congruence

## Problem

OEIS A378576, Paul D. Hanna, Dec 01 2024, states the following NAME and
COMMENT, reproduced verbatim from `Library/Recurrence/hanna2024a378576.md`:

> G.f. A(x) satisfies A(x) = x + x*A(A(A(A(A(A(x)))))), so that this sequence shifts left under the 6th self-COMPOSE.

> Conjecture: a(n) == 1 (mod 5) for n >= 1.

## Motivation

This is a first-tier OEIS conjecture from the 2024 entry. The target is the
assertion for every positive index, with KPI = open problems resolved.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
independently repeat those source or literature searches.

## Route

The module is parametrised by the iterate count r. The integer coefficients
`a r n` and series `generatingSeries r` give the unique normalised solution of
`A = X + X * iterate A r`, where `iterate` is the r-fold compositional iterate
from the frozen `CompositionalIterateCongruence`. A private shifted-iterate
degree contraction over arbitrary commutative rings constructs the stabilised
fixed point. For `2 <= r`, `generating_equation` states `A(0) = 0`, `a(1) = 1`,
and the equation; `generating_unique` covers every zero-constant integer
solution, without separately assuming its linear coefficient.

For `2 <= r`, `2 <= m`, and `m` dividing `r - 1`, `mod_identity r m` identifies
the image in `ZMod m` with `mobius 1`, the formal series `X/(1-X)`. The frozen
`mobius_iterate` identity and `r = 1` in `ZMod m` make the r-fold iterate of
`mobius 1` equal to itself; geometric-series algebra and uniqueness over the
reduced ring identify the fixed points. Extracting coefficients gives the
general theorem `shift_iterate_mod`: `a r n % m = 1` for every `n >= 1`.

The anchor `hanna_conjecture_six` specialises this result to `r = 6, m = 5`.
OEIS A378575 is the sibling instance `r = 5, m = 4`, proved by
`hanna_conjecture_five` and recorded with its own resolution claim in
`Problems/oeis-a378575-shifted-iterate-fixed-point-mod-four.md`.
Target generality is I because the module imports the frozen G provider
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence`, statement_id
`sha256:4063c4732963765b6b16b5dda51775b4d179cfc3a203c91ed15e3ebffb0467e7`.

## Falsifier

A positive index n whose coefficient in the normalised six-fold solution
has remainder other than 1 modulo 5 would falsify the assertion. The
orchestrator's exact coefficient check is supporting evidence only, not a
substitute for the universal proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/ShiftedIterateFixedPointCongruence.lean`.
- Public theorem and sole resolution anchor: `hanna_conjecture_six`.
- Companions: `generating_equation`, `generating_unique`, `mod_identity`, and
  the general theorem `shift_iterate_mod`; both OEIS instances specialise it.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported for
  all six public theorems by the implementation seat.

## Triage

`theorem`. The instance proves the universal assertion recorded by OEIS A378576.

## ASSUMED-UNVERIFIED

The quotations were supplied by the orchestrator and checked here against the
Library note. The OEIS entry and revision history were read by the search
seat on 2026-09-09, not by this seat, which had no network access. The reported
literature scope was identifier search on arXiv, MathOverflow, and GitHub;
absence of a found proof is not an exhaustive bibliography or a priority
claim. Source-to-Lean identification and first-publication priority are not
kernel-checked facts. The orchestrator's numerical check and external build
reports were supplied evidence rather than computations repeated by this seat.
