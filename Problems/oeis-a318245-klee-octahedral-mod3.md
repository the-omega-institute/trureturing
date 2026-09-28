---
slug: oeis-a318245-klee-octahedral-mod3
bibkey: klee2018a318245
doi: null
url: https://oeis.org/A318245
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result
---

# Klee's conjecture 3 | a(n) for OEIS A318245

## Problem

OEIS A318245 (Bradley Klee, 2018) defines a(n) by its scaled generating
function: T(v) = Σ a(n)(3v/64)^n satisfies
9(5v−4)T + d/dv(16v(v−1)(3v−4)T') = 0 with a(0) = 1. Equivalently a(1) = 12 and
3n²a(n) = 4(28n²−28n+9)a(n−1) − 64(4n−5)(4n−3)a(n−2) for n ≥ 2. The entry
states:

> For n > 0, a(n) mod 3 = 0 (conjecture, tested up to n=3\*10^6).

Issue #11173 fixes the reading: a is defined over ℚ by the recurrence, and the
claim is that a(n) is an integer divisible by 3 for every n ≥ 1.

## Motivation

The period function T(v) measures the precession of the angular momentum
vector J along a curve of the rotational energy surface of an octahedral
molecule (Harter–Patterson 1984). Gegelia–van Straten (2026) list the sequence
as O(4), the period sequence of the elliptic surface 234III.
`D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.result` proves the
conjecture.

## Gap

Issue #11173 preregisters the route and the literature check. The entry and
its linked documents contain no proof. Gegelia–van Straten give a Laurent
polynomial representation of the sequence, supported by an ansatz search and
numerical verification. They say that such representations imply or suggest
Lucas-type congruences, but they state no congruence for this sequence and do
not mention the conjecture. `not-found-in-searched-scope`.

## Route

1. With t(k, j) = C(2k,k)·C(2j,j)·C(2k+j,k)·4^j, the sum b(n) of t(k, j) over
   k + j = n satisfies the recurrence, by a telescoping (Zeilberger)
   certificate. Hence a = b.
2. By Lucas' theorem at 3, t(3i+s, 3a+e) ≡ t(s,e)·t(i,a) (mod 3) for s, e < 3.
   Hence b(3m+r) ≡ b(r)·b(m) (mod 3).
3. b(1) = 12, b(2) = 180 and b(0) = 1 give 3 | b(n) for n ≥ 1 by strong
   induction.

## Falsifier

The proof would fail if the certificate identity failed at some k, if a
boundary term were missed, or if a carry in Lucas' theorem produced a
nonvanishing term.

## Evidence

Exact computation (issue #11173): a(n) is an integer and 3 | a(n) for
1 ≤ n < 400, with 12 | a(n) as well. The closed form equals a(n) for n < 400.
The controls "9 | a(n)" and "24 | a(n)" fail.

The canonical source is
`D5/S3/Quantum/Molecular/OctahedralPrecessionPeriods.lean`. Its public
declarations are `a`, `claim` and `result`. The frozen module state has
statement identity `sha256:304224c4273a134eabbe22b1cf986a47f75f2d910be27f2e7cb586fcef1abdea`.
The result declaration has statement identity
`sha256:8d0859b0b0a905141888de26d490751d4168c2b0244a318c9dcb7ffe62d57021`.
The Freeze event is
`sha256:9b19a24a8ea66a50b536abdcc7fc1316c51ca3f2f803376f067df091361bf690`.
It has no project-level frozen prerequisite. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture (an OEIS formula-line conjecture of 2018),
preregistered in issue #11173 before any Lean. `theorem`; resolution
`proved`. The public theorem has `proof_shape: content`: the closed form with
its certificate and the multiplicativity modulo 3 are new propositions on its
live path. Admission basis `open-problem-resolution`; utility `none`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
