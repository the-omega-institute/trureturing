---
slug: oeis-a000364-secant-number-pure-period-refutation
bibkey: bala2023a000364
doi: null
url: https://oeis.org/A000364
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation
---

# Refutation of the A000364 pure-periodicity conjecture

## Problem

OEIS A000364, NAME (verbatim from `Library/Recurrence/bala2023a000364.md`):

> Euler (or secant or "Zig") numbers: e.g.f. (even powers only) sec(x) = 1/cos(x).

COMMENT (verbatim; attributed in that Library note to Peter Bala, May 08 2023):

> Conjecture: taking the sequence [a(n) : n >= 1] modulo an integer k gives a purely periodic sequence with period dividing phi(k). For example, the sequence taken modulo 21 begins [1, 5, 19, 20, 16, 2, 1, 5, 19, 20, 16, 2, 1, 5, 19, 20, 16, 2, 1, 5, 19, ...] with an apparent period of 6 = phi(21)/2.

## Motivation

This first-tier OEIS conjecture was entered as a comment in 2023. The KPI is
open problems resolved: a certified counterexample resolves the named claim.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and searching the identifier on arXiv,
MathOverflow and GitHub. This Stage-B seat has no network access and did not
repeat those searches. This is a bounded literature-search report, not a
claim of exhaustive coverage or first-publication priority.

## Route

The escape content is strong induction reducing the integer recurrence
`a 0 = 1`, `a n = Σ_{j=1..n} (−1)^{j+1} C(2n,2j) a(n−j)` into `ZMod 27`
at every index. This keeps the arithmetic inside 27 residues instead of
evaluating a 37-digit integer. It carries the two residue certificates
`(a 1 : ZMod 27) = 1` and `(a 19 : ZMod 27) = 10`. Since `φ(27) = 18`,
pure periodicity with a positive period dividing 18 would force
`a(1) ≡ a(19) (mod 27)`, a contradiction. `Function.Periodic.nat_mul`
transports any proposed dividing period to the shift by 18.

This certified instance has the sole purpose of refuting a named claim,
the admissible case under the repository's utility rule. The Lean header
therefore declares `kind=certified-instance; basis=refutes` with the explicit
claim `balaConjecture` and result `bala_conjecture_false`, rather than
`utility: none`. Target generality: G. Imports are Mathlib-only.

## Falsifier

The counterexample index is `n = 1` at `k = 27`: shifting by `φ(27) = 18`
compares indices 1 and 19, whose residues are 1 and 10. A correction to these
residues or to the identification of the recurrence with A000364 would
invalidate this proposed refutation. The orchestrator's exact integer check
is supporting evidence only; the Lean residue certificates supply the proof.

## Evidence

- Lean module: `D5/S1/Recurrence/Periodic/SecantNumberPurePeriodRefutation.lean`.
- Main theorem: `bala_conjecture_false : ¬ balaConjecture`; the resolution
  claim is `Refuted` and is attached only to this theorem.
- Companions: recurrence characterisation `a_recurrence`, uniqueness
  `a_unique`, `initial_values`, reduction lemma `reduction`, and residue
  certificates `residue_one` and `residue_nineteen`. Public definitions:
  `a`, `b`, `balaConjecture`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat for all ten public declarations.
- Supporting measured readings supplied by the orchestrator from
  `results/verify-r16.out`: exact integer computation of 210 terms using
  `a(n) = Σ_{j=1..n} (−1)^(j+1) C(2n,2j) a(n−j)`, reproducing the published
  DATA. The property FAILS at `k = 27` (`a(1) ≡ 1`, `a(19) ≡ 10`,
  `φ(27) = 18`), at `k = 81`, at `k = 125`, and at `k = 243`
  (`a(2) ≡ 5`, `a(164) ≡ 167`, `φ(243) = 162`). It HOLDS at `k = 9`
  and `k = 25` in the checked range. Only the `k = 27` refutation is
  formalized; all other moduli are unformalized numerical observations.
- The word that fails is **"purely"**. Modulo 27, the shift by 18 holds for
  every `n` from 2 to 192 in the checked range, while it fails at `n = 1`.
  This exhibits the eventually periodic pattern with a transient of exactly
  one term within that range; eventual periodicity at all indices is not
  proved by either the finite check or this module.
- This does not contradict the Knuth–Buckholtz theorem cited in the entry
  (pure periodicity modulo an odd **prime**). The counterexamples are at
  prime **powers**.

## Triage

`theorem`. A certified counterexample refutes the universal conjecture via
its modulus-27 specialization; one dossier records the `Refuted` resolution.

## ASSUMED-UNVERIFIED

The OEIS quotations and numerical readings were supplied by the orchestrator.
The OEIS revision history was read by the search seat, not this seat; literature
scope was the entry, revision history and identifier searches on arXiv,
MathOverflow and GitHub on 2026-09-09. This seat had no network access and did
not inspect `results/verify-r16.out`, which was absent from this worktree.
The recurrence-to-source identification, attribution and publication priority
are not kernel-checked facts. The Library note attributes the comment to
Peter Bala; the brief's earlier Paul D. Hanna attribution is inconsistent
with that supplied source and was not independently verified. Numerical
observations outside the formalized modulus-27 refutation, including the
finite eventual-periodicity pattern, are unformalized.
