---
slug: bartoli-stanica-reduced-critical-point-conjecture
bibkey: bartoli2026apn
doi: null
url: https://arxiv.org/abs/2608.30808
triage: theorem
motivation_gids:
  - D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation
---

# Bartoli--Stănică reduced critical-point conjecture

## Problem

Daniele Bartoli and Pantelimon Stănică, *Reduced polynomial lifts of APN
permutations over Galois rings and effective non-APN bounds*,
arXiv:2608.30808v1 (31 August 2026), Conjecture 2 in Section 2 states:

> For every q = 2^m, the reduced representative f ∈ F_(q)[x] of every APN
> permutation of F_(q) has a critical point in F_(q).

Here APN means differential uniformity exactly two. The reduced representative
has degree less than q and the critical point is a finite rational a with
`f'(a) = 0` in the same field. The dossier addresses this exact universal
statement. It does not assert a result about unnormalized polynomial lifts,
affine-invariance, Galois-ring permutations, or non-rational ramification.

## Motivation

Conjecture 2 is a named open problem in a current arXiv paper. A single
source-faithful finite field and reduced polynomial satisfying all APN and
permutation hypotheses while having nowhere-zero formal derivative refutes the
universal statement.

## Gap

Conjecture 2 asks whether bijectivity and differential uniformity exactly two
force a rational zero of the formal derivative of the same reduced polynomial.
The Lean result refutes this implication at q = 32: the degree-24 polynomial
is bijective and exactly APN, but its derivative is nonzero at every field
element. This resolves only the literal finite-field claim; global publication
priority remains `ASSUMED-UNVERIFIED`.

## Route

Use the field with 32 elements represented by five-bit vectors for
`F_2[t]/(t^5+t^2+1)`. XOR is addition; carryless multiplication is reduced by
the binary modulus 37. Define one degree-24 polynomial with the supplied 16
nonzero coefficients. Its evaluation labels form a bijection on all 32 field
elements. Kernel computation checks every one of the 992 pairs consisting of a
nonzero direction and a target: each differential fiber has size at most two.
The fiber for direction label 1 and target label 16 is exactly `{24,25}`, so
the APN value is exactly two. The same polynomial has a nonzero formal
derivative at each of the 32 field elements.

Applying the universal claim at `m = 5`, this field, and this polynomial would
produce a derivative zero, contradicting the computed nowhere-zero derivative.

## Evidence

- Lean module: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.lean`.
- Claim declaration: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim`.
- Result theorem: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.result`.
- The result has type `Not claim` and its kernel axiom closure is exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The source polynomial has degree 24, strictly below q=32, and all hypotheses
  use this same Polynomial. Labels are field vectors, not Nat casts or ZMod 32.

The prior numerical verification checked all 32 evaluations, all 32 derivative
values, and all 992 differential fibers for the fixed coefficients. The Lean
build independently kernel-checks the same finite computations. This record
does not claim that the supplied bounded literature searches prove global
priority.

## Falsifier

A proof of the universal Conjecture 2 would falsify the result theorem. Within
the formal statement, a mismatch in the coefficient table, a degree or field
model mismatch, a non-bijective evaluation, a fiber above two, loss of exact
size-two attainment, or any derivative zero would invalidate this refutation.

## Triage

`theorem`. The result is a direct finite refutation of the literal universal
Conjecture 2. The proof-shape assessment is `content` with admission basis
`escape-witness`: the field-law construction, actual evaluation bridge,
bijection, complete fiber bound, exact attainment, and nowhere-zero derivative
all occur on the live proof path. No standalone positive witness package or
new named bind-only theorem is introduced.

## ASSUMED-UNVERIFIED

The caller's source and bounded search evidence found no prior direct
resolution, but the searches are not exhaustive. Global publication priority
and any claim beyond Conjecture 2 remain `ASSUMED-UNVERIFIED`.
