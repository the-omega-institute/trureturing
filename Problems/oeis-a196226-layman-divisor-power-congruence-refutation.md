---
slug: oeis-a196226-layman-divisor-power-congruence-refutation
bibkey: layman2011a196226
doi: null
url: https://oeis.org/A196226
triage: theorem
motivation_gids:
  - D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation
---

# Refutation of Layman's A196226 divisor-power congruences

## Problem

OEIS A196226 defines its terms as the natural numbers `m` for which the sum
of divisors of `m`, reduced modulo `m`, is `3 + m/2`. John W. Layman's
conjecture comment gives three universal congruences:

> (1) If m>=14 is a term of this sequence, then sigma(2,m) is congruent to
> 5 + m/2 modulo m.

> (2) If m>=22 is a term of this sequence, then sigma(3,m) is congruent to
> 9 + m/2 modulo m.

> (3) If m>=38 is a term of this sequence, then sigma(4,m) is congruent to
> 17 + m/2 modulo m.

Here `sigma(k,m)` is the sum of the `k`-th powers of the positive divisors
of `m`. The formal membership predicate makes the entry's evenness condition
explicit:

```lean
def membership (m : Nat) : Prop :=
  2 | m /\ ArithmeticFunction.sigma 1 m % m = 3 + m / 2
```

Natural-number division is used throughout. The closed `claim` is the
disjunction of the three displayed universal statements, so `Not claim`
asserts that every one of the three conjectures is false.

## Motivation

The same value tests all three clauses. The value `m = 690` is an A196226
term above all three thresholds and is not an even semiprime. An exact
certificate at that value settles the three literal OEIS assertions without
proposing a corrected conjecture.

The first-tier external problem was preregistered in issue
https://github.com/the-omega-institute/trureturing/issues/8955 before the
numerical and Lean probes. That registration records the complete quantified
clauses, the source revision, the intended counterexample, and the bounded
literature reading.

## Gap

`dominating_theorem_search: not-found-in-searched-scope`. The preregistration
read the complete OEIS A196226 text at revision 21 and found the three lines
still labelled as conjectures. The entry has no paper link giving a proof or
refutation. Repository searches at the registered base found no A196226,
A054024, or matching divisor-power congruence declaration in D5, Blueprint,
Library, Problems, or the frozen ledger. The late collision search at
`origin/dev` commit `14a9a189a5bf636024f4a49602f9f9c7e2aad313` found no
exact-name or counterexample-value match. Pinned Mathlib contains the divisor
power sum and modular-congruence machinery used by the certificate, but no
theorem settling these A196226 statements was found in the searched scope.

The searched surfaces do not establish exhaustive literature absence, and no
publication-priority claim is made.

## Route

At `m = 690`, exact divisor-power sums are

```text
sigma(1,690) = 1728
sigma(2,690) = 689000
sigma(3,690) = 386358336
sigma(4,690) = 244202442248
```

The first identity gives `1728 mod 690 = 348 = 3 + 690/2`, and `690` is even,
so `membership 690` holds. It also exceeds the thresholds 14, 22, and 38.
The remaining remainders are

```text
689000 mod 690       = 380, while 5  + 690/2 = 350
386358336 mod 690    = 426, while 9  + 690/2 = 354
244202442248 mod 690 = 668, while 17 + 690/2 = 362
```

Thus the required congruence fails in each branch. The Lean proof computes
the four exact sums with kernel reduction, establishes membership, and derives
a contradiction from each possible disjunct.

## Falsifier

Any failure of the exact membership calculation, threshold comparisons, or
one of the three divisor-power sums would invalidate the corresponding
branch. A proof of any one of the three universal conjectures would contradict
the kernel-checked theorem `result : Not claim`.

## Evidence

The canonical source is
`D5/S0/Certificates/LaymanDivisorPowerCongruenceRefutation.lean`. Its authored
declarations are exactly `membership`, `claim`, and `result`; there are no
public helper theorems. The frozen module state has statement identity
`sha256:1e50fb2689c9aee86b807db4fc2ab71c93b28e8d900f012f66464ecf041e0b67`.
The result declaration has statement identity
`sha256:8ab5bb3e64293e51281e472149b3254109ea5764739fe6b7c202a68c7e63c608`.
The Freeze event is
`sha256:3cab529d6597c5c1fe5be6b648acf80bc7a129c40fe32ba07948b8775c161de3`
and has no project-level frozen prerequisites; both direct imports are pinned
Mathlib modules.

The result is a closed typed refutation of `claim`. Its utility classification
is `certified-instance` with `basis=refutes` directed to that claim. The proof
uses no `sorry`, `native_decide`, or new axiom.

## Triage

`theorem`; resolution `refuted` for all three quoted Layman congruence
conjectures. The public theorem has `proof_shape: bind-only` because the exact
arithmetic is normalization over pinned Mathlib definitions.
`admission_basis: open-problem-resolution` under preregistration issue #8955;
`escape_witness: none`. The definitions encode the external statement and the
single public theorem is the permitted named open-problem settlement. There is
no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

Exhaustive publication coverage and priority were not verified and are not
claimed. Source-to-Lean fidelity and the proof-shape and utility
classifications remain semantic review judgments, separate from kernel type
checking. No least-counterexample theorem is claimed; `690` is used only as a
valid simultaneous counterexample.
