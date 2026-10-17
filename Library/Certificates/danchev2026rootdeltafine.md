---
bibkey: danchev2026rootdeltafine
authors: P. Danchev; O. Hasanzadeh; A. Moussavi; A. Javan
year: 2026
title: sqrt(Delta)-Fine Rings
doi: 10.48550/arXiv.2608.30734
url: https://arxiv.org/html/2608.30734v2
claim: Displayed Problem 4.4 asks whether a root-Delta-fine ring which is not fine exists.
strata_touched:
  - D5/S0/Certificates/RootDeltaFineRings
license: citation-only
triage: anchor
---

# Root-Delta-fine rings and displayed Problem 4.4

## Locator

The source is arXiv:2608.30734v2, DOI `10.48550/arXiv.2608.30734`, at
https://arxiv.org/html/2608.30734v2, revised 2026-10-11. The cited clauses are
Introduction S1.p1, S1.p4, S1.p6 and S1.p7, Definition 2.1, and the displayed
Problem 4.4 in Section 4, HTML S4.Thmtheorem4. Its standing convention
in Introduction paragraph S1.p1 is an arbitrary associative ring with identity,
which need not be commutative. The formalization includes infinite rings and
the trivial ring and is polymorphic in the carrier universe.

## Definitions and resolution

Introduction S1.p6 gives the explicit characterization used here:

> An element a belongs to Delta(R) if and only if 1 - u*a belongs to U(R)
> for all u in U(R).

The multiplier is on the left. Lean's `Rˣ` consists of two-sided units;
`IsUnit` asserts that an element is the value of such a unit. Introduction
S1.p7 defines root-Delta by membership of some power with exponent at least
one. Definition 2.1 requires every nonzero element r to have a decomposition
r = u + a with u a unit and a in root-Delta. Only the separately named strong
variant imposes commutation. Introduction S1.p4 defines fine by the same
nonzero-element decomposition with a nilpotent summand.

The displayed question in Section 4, HTML S4.Thmtheorem4, is:

> **Problem 4.4.** Is there a sqrt(Delta)-fine ring which is not fine?

The answer proved by `RootDeltaFineRings.rootDeltaFine_implies_fine` is No.
More strongly, `delta_eq_zero` proves every Delta member is zero, while
`zero_delta` supplies the reverse containment. `rootDeltaFine_iff_fine`
proves the equivalence. In the trivial ring the nonzero-element conditions
are vacuous; the proofs retain this case.

For a nonzero Delta member d, write d = u + a using the ring hypothesis.
The Delta test at u inverse makes b = 1 - u inverse * d a unit. Associativity
and the two-sided inverse laws give (-u)*b = d-u = a, with that product order.
Thus a and every power of a are units. A Delta member cannot be a unit in a
nontrivial ring: its inverse would make the Delta test zero. The positive
power witnessing root-Delta membership yields the contradiction. Consequently
Delta is zero, so every root-Delta summand is nilpotent. Conversely, from a
nilpotency exponent n the proof uses n+1 to obtain a strictly positive zero
power; zero always belongs to Delta. No radical or quotient theorem is used.

The paragraph immediately before the question conjectures existence, whereas
the concluding discussion conjectures the universal implication. The
introductory radical-description prose also has an inconsistent containment
description. The formalization uses the explicit unit-test characterization
and answers the displayed existence question; these other prose assertions
are not premises or independently certified claims.

The independently audited HTML is 405596 bytes with SHA-256
`e0286bce9e4472ba30c7a1118c20b51e270dedc63f6c756482ea6f1dd0aacbf7`.
The author TeX file `Delta-Fine_Final.tex` is 53149 bytes with SHA-256
`97fd75844d5749434eea3a2ba9c2d7617662b20e7c24ca6171c7fb86c1913fa6`.
Its relevant clauses are lines 197, 203, 207, 209, 227–235 and 776–778.
The HTML identity was also independently rechecked for this delivery.
Global prior publication and priority remain `ASSUMED-UNVERIFIED`; this note
makes no claim of exhaustive literature clearance or first discovery.
