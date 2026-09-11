---
slug: oeis-a396102-triple-iterate-shift-mod-three
bibkey: hanna2026a396102
doi: null
url: https://oeis.org/A396102
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/TripleIterateShiftModThree
---

# G.f. A(x) satisfies A(A(A(x))) = (1+x) * A(A(x))

## Problem

NAME "G.f. A(x) satisfies A(A(A(x))) = (1+x) * A(A(x))."

COMMENT "Conjecture: a(n) == 1 (mod 3) for n >= 1."

These are the verbatim NAME and COMMENT lines supplied for OEIS A396102 by Paul D. Hanna, Jun 06 2026.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems resolved.

## Gap

No proof was found: the OEIS entry and revision history were read by the search seat on 2026-09-09, and identifier searches covered arXiv, MathOverflow, and GitHub. This seat has no network.

## Route

The integer construction is a degree-contracting correction map on diagonal coefficients (`generating_equation`: `A(0) = 0`, `a(1) = 1`, and `A∘3 = (1 + X)·A∘2`, with `iterate` from the frozen `CompositionalIterateCongruence`). Uniqueness over ℤ and over `ZMod 3` uses the live first-difference lemma: the first differing coefficient of two agreeing series enters the j-fold compositional iterate with multiplicity j, so `f + (1 + X)·iterate f 2 − iterate f 3` gains one degree of agreement because `1 + 2 − 3 = 0` (`generating_unique`). Over `ZMod 3`, `mod_three_fixed` verifies that the geometric series `mobius 1 = X/(1 − X)` (frozen `mobius`, with `iterate mobius j = X/(1 − jX)` via frozen `mobius_iterate`) satisfies the same equation since iterate 3 = X over `ZMod 3`; uniqueness identifies A mod 3 with `mobius 1`, and `hanna_conjecture` reads off `a(n) ≡ 1 (mod 3)` for n ≥ 1. Freeze prerequisite: the frozen `CompositionalIterateCongruence` module (generality G).

## Falsifier

A counterexample index n ≥ 1 with `a(n) % 3 ≠ 1` would falsify the conjecture. The orchestrator's exact finite check is supporting evidence only.

## Evidence

- Module: `D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.lean`.
- Main theorem: `hanna_conjecture`.
- Companions: `generating_equation`, `generating_unique`, `mod_three_fixed`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

The quotes are supplied by the orchestrator. The OEIS revision history was read by the search seat, not by this seat. The literature scope is the OEIS entry and revision history plus identifier searches on arXiv, MathOverflow, and GitHub; this seat has no network.
