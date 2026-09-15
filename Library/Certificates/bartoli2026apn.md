---
bibkey: bartoli2026apn
authors: Daniele Bartoli; Pantelimon Stănică
year: 2026
title: "Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds"
doi: null
url: https://arxiv.org/abs/2608.30808
claim: "Conjecture 2 states that the reduced representative of every APN permutation over F_(2^m) has a critical point in F_(2^m)."
strata_touched:
  - D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation
license: citation-only
triage: anchor
---

# Bartoli--Stănică reduced critical-point conjecture

Daniele Bartoli and Pantelimon Stănică, *Reduced polynomial lifts of APN
permutations over Galois rings and effective non-APN bounds*, arXiv:2608.30808v1
(31 August 2026), state in Section 2:

> For every q = 2^m, the reduced representative f ∈ F_(q)[x] of every APN
> permutation of F_(q) has a critical point in F_(q).

Their Definition 1.1 defines APN by differential uniformity exactly two. The
paper's reduced representative is the unique polynomial of degree less than
q inducing the field function. A critical point here is a finite rational point
a in the same field with the formal derivative f'(a) = 0. This note records
Conjecture 2 only; the Galois-ring lifting statement, unnormalized lifts,
affine-invariance claims, and algebraic-closure ramification claims are outside
the formalized statement.

## Verified locator

- URL: https://arxiv.org/abs/2608.30808
- Version: v1, dated 2026-08-31.
- Source locator: Section 2, Conjecture 2, immediately after Theorem 2.2.
- Source capture used for this entry: the supplied v1 text and HTML metadata;
  the capture SHA-256 is `1d0c2ba21b6416102049b3c2e2770c7917086a2c9b1c19459937f4d8515c9ba3`.

## Formal scope

The Lean claim quantifies over every positive natural m, every finite
characteristic-two field K with `Fintype.card K = 2^m`, and every polynomial f
whose degree is less than `2^m`. It requires bijective evaluation and the exact
APN condition: all nonzero-direction/target fibers have cardinality at most two
and one such fiber has cardinality two. Its conclusion asks for a zero of the
formal derivative in K.

The refutation instantiates m = 5 with one actual field of 32 five-bit vectors.
Addition is XOR and multiplication is carryless multiplication reduced by
`t^5 + t^2 + 1` (binary modulus 37). The same degree-24 Polynomial is used in
the evaluation, differential fibers, and derivative. Its 16 nonzero
coefficients and 32 evaluation labels are the supplied fixed witness. Exact
APN attainment occurs at direction label 1 and target label 16, with points 24
and 25; all 992 nonzero-direction/target fibers are checked. The derivative is
nonzero at every field element.

The labels are binary coefficient vectors in the field model. They are not
natural-number casts and the model is not `ZMod 32`. The degree-24 inequality
against q=32 is retained as the reduced-representative normalization.

## Search and priority boundary

The caller's bounded D5, pinned Mathlib, and admissible third-party searches
found no dominating APN refutation or matching theorem. The 4.34.0-rc2
hex-poly-fp package was not added to this Lean 4.33.0 project. These searches
are bounded and do not establish exhaustive literature coverage or global
publication priority; priority remains `ASSUMED-UNVERIFIED`.

## Formal record

The canonical module is
`D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.lean`.
Its sole theorem is `result : Not claim`; all finite field construction,
evaluation, exact fiber computation, attainment, and derivative computation
remain live in that proof. The accepted axiom closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`.
