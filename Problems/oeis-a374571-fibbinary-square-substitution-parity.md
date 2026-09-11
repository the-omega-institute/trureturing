---
slug: oeis-a374571-fibbinary-square-substitution-parity
bibkey: hanna2024a374571
doi: null
url: https://oeis.org/A374571
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity
---

# Fibbinary parity of the A374571 coefficients

## Problem

OEIS A374571 (Paul D. Hanna, Jul 11 2024), quoted verbatim from the claim in
`Library/Arith/hanna2024a374571.md`:

NAME:
> Expansion of g.f. A(x) satisfying A(x) = A(x^2) - x*A(x^2)^2.

COMMENT:
> Conjecture: for n > 0, a(n) is odd iff n = A003714(k) for some k > 0, where A003714 lists Fibbinary numbers whose binary representation contains no two adjacent 1's.

The formalization uses the normalization A(0) = 1 and the bitwise predicate
`Fibbinary n := n &&& (n >>> 1) = 0` for no adjacent one bits.

## Motivation

This is a first-tier recent OEIS conjecture, selected for a universal proof.
KPI = open problems resolved, rather than module count or finite examples.

## Gap

The supplied search-seat report found no proof in its searched scope: the OEIS
entry and revision history were read on 2026-09-09, and identifier searches were
made on arXiv, MathOverflow, and GitHub. This Stage-B seat had no network access
and did not repeat those searches. This is a bounded literature-search report,
not a claim of exhaustive coverage or first-publication priority.

## Route

The integer sequence a is defined by the exact recursion a(0) = 1,
a(2n) = a(n), and a(2n+1) = −Σ_{j≤n} a(j)·a(n−j). The implementation is
well-founded, with multiplier 1; every recursive index in the positive-degree
clause is smaller than the index being defined. `generating_equation` proves
A(0) = 1 and A = A(X²) − X·A(X²)² by coefficient comparison.
`generating_unique` proves that every integer formal power series B with
constant coefficient 1 satisfying that equation equals A. The equation leaves
the constant term free, so the constant-coefficient hypothesis is essential.

Over ZMod 2, `binary_recurrence` reduces the proved generating equation through
Frobenius to ā(2n) = ā(n), ā(4m+1) = ā(m), and ā(4m+3) = 0. Then `parity_all`
matches that descent by strong induction against the independently proved
adjacent-bit recursions of `Fibbinary n := n &&& (n >>> 1) = 0`: remove an ending
zero, remove an ending 01, and exclude an ending 11. This is the no-two-adjacent-
ones condition for OEIS A003714. The public `hanna_conjecture` gives
`Odd (a n) ↔ Fibbinary n` for n > 0; the internal parity result also includes
zero. The module has Mathlib-only imports, no D5 import, and generality G.

## Falsifier

A positive counterexample index n for which exactly one of `Odd (a n)` and
`Fibbinary n` holds would refute the assertion. The orchestrator's exact finite
check is supporting evidence only; it does not prove the unbounded theorem.

## Evidence

- Lean module: `D5/S1/Recurrence/Parity/FibbinarySquareSubstitutionParity.lean`.
- Main theorem: `hanna_conjecture`.
- Companion theorems: `generating_equation`, `generating_unique`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`) for each public
  theorem, as reported by the implementation-seat axiom check.

The Lean definition is:

```lean
def Fibbinary (n : ℕ) : Prop := n &&& (n >>> 1) = 0
```

This is the standard characterisation of A003714: bit i of the intersection
is the conjunction of bits i and i+1 of n, so a zero intersection means that
the binary representation has no two adjacent ones. The private
`fibbinary_bits` and `fibbinary_bit` establish this bit interpretation and its
descent rules independently of the coefficient sequence.

## Triage

`theorem`. The formal proof closes the universal positive-index assertion
recorded by OEIS under the stated normalization.

## ASSUMED-UNVERIFIED

The quotations, author, and date were supplied by the orchestrator; this seat
copied the quotations from the Library note. The OEIS revision history was
read by the search seat, not by this seat. Literature scope was the OEIS entry
and revision history plus identifier searches on arXiv, MathOverflow, and
GitHub on 2026-09-09; no independent network verification was performed by
Stage-B. Exhaustive literature coverage, first-publication priority, and the
source-to-Lean identification are not kernel-checked facts. The orchestrator's
exact numerical check and prior build results were supplied evidence, not
Stage-B reruns.
