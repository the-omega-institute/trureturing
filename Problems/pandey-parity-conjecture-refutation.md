---
slug: pandey-parity-conjecture-refutation
bibkey: pandey2026parity
doi: null
url: https://arxiv.org/abs/2601.03293v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial_eval
---

# Pandey's Parity Conjecture 4.1

## Problem

Rohan Pandey, arXiv:2601.03293v1, Conjecture 4.1 (Parity Conjecture),
PDF page 4:

> For all integers n ≥ 2k+1, the independence polynomial I(GP(n,k),x) has only real roots if and only if k is even.

Definition 2.1 supplies `n >= 3` and `1 <= k < n/2`. Precisely, for every
`n,k : Nat` with `3 <= n`, `1 <= k`, and `2*k < n`, the assertion is
`(forall z : Complex, eval₂ (Int.castRingHom Complex) z
(independencePolynomial (gp n k) univ) = 0 -> z.im = 0) <-> Even k`.
The polynomial is the existing integer independent-set generating
polynomial on all vertices. No experimental-range restriction is added.

## Motivation

The frozen `IndependentPartitionDeletion.independencePolynomial_eval`
relates this actual polynomial to its weighted independent-set sum.
It allows an exact graph counterexample to address the published
biconditional without assuming a transfer-matrix formula or approximate
root calculations.

## Gap

There is no remaining gap in the resolution of this exact conjecture.
The earlier public [refutation](https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md)
already gives `GP(3,1)` with polynomial `1+6x+6x^2` and an explicit
opposite-parity isomorphism `GP(7,2) -> GP(7,3)` that contradicts the
full biconditional. Its provider commit timestamp is
`2026-06-13T01:23:03Z`; its internal June 11 date is unverified.
The [prior-refutation Library note](../Library/Combinatorics/demonstrandum2026pandeyrefutation.md) pins the
commit, blob, and source hash and explains the edge map. This evidence
supersedes the bounded no-hit screen for
[issue 8619](https://github.com/the-omega-institute/trureturing/issues/8619)
and invalidates the historical `open-problem-resolution` novelty
admission. The local contribution is a formalization of a known
refutation, not an eligible newly solved open problem.

## Route

Use vertices `Bool x Fin n`, representing `u_i` and `v_i`, and the
undirected, loop-free closure of the source's outer-successor,
inner-`k`-step, and equal-index spoke relations, with indices modulo `n`.
At `n=3,k=1`, all source hypotheses hold. The independent sets are
exactly the empty set, the six singletons, and the six cross-layer pairs
with different indices. Their generating polynomial is `1+6X+6X^2`.

For a complex zero `z=a+bi`, the imaginary equation is
`6b(1+2a)=0`. If `b != 0`, then `a=-1/2`, and the real equation becomes
`-1/2-6b^2=0`, impossible since `b^2 >= 0`. Thus every complex root
is real, whereas `Even 1` is false. This refutes the forward implication
and hence the full universal biconditional.

## Falsifier

A source restriction excluding `n=3,k=1`, an incorrect graph-to-source
mapping, or a failure of the exact independent-set enumeration would
invalidate this refutation. The prior-resolution falsifier of novelty
admission is satisfied by the exact public refutation cited above;
that correction does not invalidate the mathematical counterexample.

## Evidence

The formal carrier and sole public result `result : Not claim` are in
`D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.lean`.
The proof uses kernel `decide` for the configuration equality, the frozen
evaluation bridge, finite-sum simplification, and exact complex arithmetic.
The matching Scribe definition attributes the result to the earlier
public refutation through its separate Library note and retains
`OpenProblemResolutionClaim(Refuted)`. Under spec §11.20.5 this records
the local theorem-to-problem binding, not worldwide novelty or the
validity of historical novelty admission.
The graph and claim retain the [Pandey Library source](../Library/Combinatorics/pandey2026parity.md).

Primary-source hashes: TeX
`5147f84b91867223e59aa63486af9b4276eadd08dc785fa40ab3c670c80ef004`;
PDF `bae13d4946674f1149b74ef9095d04d9d7ec2d4010dbd8357de52ad88cd066e2`.

## Triage

`theorem`; a published named conjecture with a known prior exact
refutation. Its historical Tier 1 selection in issue 8619 did not
establish eligibility: the `open-problem-resolution` admission basis
was invalid because the exact assertion was already resolved. The
conservative `proof_shape: bind-only` and `escape_witness: none`
remain, without a replacement admission basis or escape-witness
retrofit. The existing valid frozen mathematics is retained under
CLAUDE §§1.3 and 3.2. The computational use remains a
`certified-instance` refuting the closed full `claim`. The triangular
prism, its polynomial, and its real-rootedness are classical, including
the claw-free theorem of Chudnovsky and Seymour cited by the source.
No new family, technique, classification, or global priority is claimed.

## ASSUMED-UNVERIFIED

The public note's internal June 11 date and its numerical, enumeration,
Sturm, checker, and audit claims are unverified here; none is needed for
the explicit isomorphism contradiction or the prior-art correction.
Literature completeness beyond this exact hit is `ASSUMED-UNVERIFIED`;
no earliest-priority claim is made. Source-to-Lean fidelity requires
independent comparison with the cited version; the kernel checks the
formal statement and proof, not that prose correspondence. The typed
binding establishes neither worldwide novelty nor publication.
