---
slug: oeis-a266489-diagonal-index-divisibility
bibkey: hanna2016diagonalindex
doi: null
url: https://oeis.org/A266489
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility
---

# A266489: clause C1, index divisibility on the frozen object

## Problem

Quoted directly from the seat-local file `oeis-A266489.src`
(`seats/opB-diagidx2/oeis-A266489.src` in the supplied workspace):

> NAME: G.f. A(x) satisfies: [x^n] A( x/A(x)^n ) = 0 for n>1.
> COMMENT: CONJECTURES:
> COMMENT: (C1) n divides a(n) for n>=1: A268293(n) = a(n)/n.
> COMMENT: (C2) a(n) == 0 (mod 2) for n>=2.
> AUTHOR: _Paul D. Hanna_, Feb 07 2016

The target is only clause (C1) for this entry.
The formal object has `a(0)=a(1)=1` and exponent `e(n)=n`.
The formal vanishing condition is imposed for `n>1`, as in the quoted NAME.

## Motivation

This is a first-tier OEIS conjecture attributed to Paul D. Hanna in 2016.
The target is the unbounded assertion `n` divides this entry's `a(n)`
for every `n>=1`. This dossier and its claim account for this entry alone.

## Gap

The supplied source labels the target a conjecture. This offline follow-up
checks the entry-specific source and its connection to the delivered theorem;
it performs no new external literature or revision-history search. Whether
an earlier proof exists outside the supplied material remains unverified.

## Route

The module constructs a normalized integer power series by a triangular
coefficient update. Agreement of inverses preserves agreement of coefficients,
and each update improves agreement by one degree. Stabilization produces the
series; `generating_equation` and `generating_unique` establish its normalized
vanishing equation and uniqueness.

The coefficient engine `power_coefficient_identity` comes from differentiating
integer powers of a unit, including negative powers. In the triangular sum,
put `alpha=v_p(n)`. If `v_p(m)<alpha`, then `v_p(n-m)=v_p(m)`, so the engine
supplies the required prime-power factor in the inverse-power coefficient.
If `v_p(m)>=alpha`, strong induction supplies it in `a(e,m)`. Combining prime
multiplicities, summing and negating proves `index_power_divisibility`.
Its hypothesis `n^k | e(n)` for every natural `n` is sufficient; no claim
is made that it is the weakest sufficient hypothesis.

For this entry specialize `e(n)=n` and `k=1`.

For this entry, `agreement_a266489` identifies `a (fun m => m) n` with
`NegativePowerDiagonalModPrime.a 2 n` at every index, using the frozen
`NegativePowerDiagonalModPrime.generating_unique`. The named theorem states
C1 about that frozen coefficient function itself. This transfer is the lane's
only genuine dependency edge to the frozen sibling module. The two modules
have different exponent families; this lane does not generalize that module.

## Falsifier

A natural index `n>=1` at which `n` fails to divide this entry's
normalized coefficient would falsify the claimed conclusion.
Here the coefficient in the conclusion is the frozen `NegativePowerDiagonalModPrime.a 2 n`.
Finite agreement with DATA and finite divisibility checks cannot exclude
an arbitrary later counterexample.

## Evidence

- Lean module: `D5/S1/Recurrence/Residue/DiagonalVanishingIndexDivisibility.lean`.
- Entry-specific theorem and Scribe claim: `hanna_conjecture_a266489`.
- Exact conclusion for `n : ℕ`, `hn : 1 ≤ n`: `(n : ℤ) ∣ NegativePowerDiagonalModPrime.a 2 n`.
- General input: `index_power_divisibility`; coefficient engine:
  `power_coefficient_identity`; construction: `generating_equation` and
  `generating_unique`.
- Transfer to the existing object: `agreement_a266489`.

The orchestrator reports from `results/verify-r28.py` / `results/verify-r28.out`
that this entry's published DATA is reproduced exactly (15 terms), with
zero violations of its divisibility conjecture for `1 <= n < 16`.
These are attributed finite supporting readings, not a proof or a fresh run
by this seat.

## Triage

`theorem`. This lane settles exactly A266489 (C1), `n divides a(n)` for
`n>=1`. The separate (C2), the mod-2 congruence, was settled earlier by the
frozen module `NegativePowerDiagonalModPrime` and is not this lane's work.
The claim is attached to `hanna_conjecture_a266489`, whose conclusion concerns
`NegativePowerDiagonalModPrime.a 2` via `agreement_a266489`; it does not claim C2.

## ASSUMED-UNVERIFIED

The quotations and author date were read directly from this entry's own
local `.src` file; the file's fidelity to the live OEIS page and revision
history was not independently checked because this seat has no network.
External OEIS-to-Lean identification and publication priority are not
kernel-checked facts. No exhaustive literature search is claimed.
The numerical readings above are supplied by the orchestrator and were not
independently recomputed by this follow-up seat; they are support, not proof.
