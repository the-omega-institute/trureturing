---
slug: oeis-a266489-negative-power-diagonal-mod-two
bibkey: hanna2016a266489
doi: null
url: https://oeis.org/A266489
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime
---

# A266489: the mod-two congruence clause

## Problem

From [Library/ArithSums/hanna2016a266489.md](../Library/ArithSums/hanna2016a266489.md),
OEIS A266489, Paul D. Hanna, Feb 07 2016:

NAME:

> G.f. A(x) satisfies: [x^n] A( x/A(x)^n ) = 0 for n>1.

COMMENT:

> (C2) a(n) == 0 (mod 2) for n>=2.

The normalization is `a(0) = a(1) = 1`. Only this congruence clause is claimed.

## Motivation

This is a first-tier OEIS conjecture from the 2016 entry. KPI = open problems
resolved. The target is the congruence clause for all indices `n ≥ 2`.

## Gap

The search seat reported no proof found after reading the OEIS entry and its
revision history on 2026-09-09 and performing identifier searches on arXiv,
MathOverflow, and GitHub. This Stage-B seat had no network access and did not
repeat that literature search.

The separate divisibility clause of A266489, (C1), `n divides a(n)`, remains **OPEN**
and is deliberately not claimed. Repository triage
`Library/Words/oeis2026triage0911b.md`, section A395833, recorded an unconfirmed
integrality bridge for the divisibility route: the four words “Lagrange inversion”
cannot be treated as a proof. The congruence proof below does not close that gap.

## Route

The escape witness is the **general** theorem: for every prime `p`, the unique
normalized integer solution of `[x^n] A(x / A^e) = 0` for `n > 1`, with
`e = (p−1)(n−1)+1` and `a 0 = a 1 = 1`, satisfies `p ∣ a n` for `n ≥ 2`.
Its named instances prove A266489 (C2) at `p = 2` (exponent `n`) and the
A395833 mod-three clause at `p = 3` (exponent `2n−1`). A266489 and A395833
are different sequences, with no equivalence bridge: one theorem implies one
congruence clause of each entry, not equivalence of the entries.

Expanding the substitution gives a strictly triangular recursion with multiplier
1 on `a n`. Finite-depth approximations stabilize and construct the unique
integer solution. The update commutes with reduction modulo `p`. Rescaling the
geometric series computes the residual of `1 + X` in degree `r + 1` as
`(−1)^r · C(p·r, r)`. Mathlib's exact identity `Nat.choose_mul_right`,
`C(p·r,r) = p · C(p·r−1,r−1)` for `r > 0`, makes the residual vanish modulo
`p`, **with no Lucas theorem and no prime-power case analysis**. This uniformity
in `p` is precisely why one argument settles a clause of each entry. Uniqueness
over `ZMod p` then identifies the reduction of the integer sequence with `1 + X`,
whose coefficients above degree 1 are zero.

Negative powers are legitimate because `a 0 = 1` makes the series a unit. The
module writes `x / A^e` as `X * invOfUnit A 1 ^ e` over `PowerSeries ℤ`,
without Laurent series. It imports only Mathlib, has no D5 import, and has
generality G.

## Falsifier

An index `n ≥ 2` in the normalized A266489 sequence for which `2` does not
divide `a(n)` would falsify the claimed clause. The orchestrator's exact finite
check is supporting evidence only and cannot exclude an arbitrary later index.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime.lean`.
- Main theorem for this dossier: `hanna_conjecture_a266489`.
- Companions: `generating_equation`, `generating_unique`, and the general
  congruence `diagonal_conjecture_general`.
- The sibling instance has a separate dossier and a separate Library note.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as reported by
  the implementation seat's `#print axioms` output for all public declarations.

The orchestrator reported these readings from `results/verify-r22.out`: coefficients
solved from the defining relation in exact integer arithmetic were integral
through `n < 40` for both families. The computed sequences reproduced the
published DATA exactly for the first eleven terms of each:

- A266489: `1, 1, 2, 12, 132, 2180, 49098, 1428602, 51861128, 2290563882, 120711239660`.
- A395833: `1, 1, 3, 30, 567, 16452, 663894, 35188218, 2357921985, 194240779128, 19248797472504`.

For every `n` in `2..39`, `p` divided `a(n)` with zero violations in both
families. These finite checks are supporting evidence only, not proof. This
seat did not locate or independently read `results/verify-r22.out`; the readings
were supplied by the orchestrator.

## Triage

`theorem`. The formal result proves only the quoted congruence clause of A266489.
The separate divisibility clause is outside this resolution claim.

## ASSUMED-UNVERIFIED

The quotations and author date were supplied by the orchestrator and matched to
this dossier's own Library note. The OEIS revision history was read by the
search seat, not this seat. The reported literature search covered the OEIS
entry and revision history and identifier searches on arXiv, MathOverflow, and
GitHub; it is not an exhaustive publication-priority check. This seat had no
network access. The finite readings above are attributed to the orchestrator,
not independently reproduced here. First-publication priority and the external
OEIS-to-Lean identification are not kernel-checked facts.
