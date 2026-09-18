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

The bounded prior-resolution screen supplied with
[issue 8619](https://github.com/the-omega-institute/trureturing/issues/8619)
located no explicit resolution in source v1, the author's README/code,
or the inspected exact identifier/title/author/public-repository searches.
Unavailable citation APIs and challenged general engines limit this
evidence. The Library note records the classical ingredients; their
novelty is not a premise of this candidate.

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
invalidate this refutation. A located prior resolution of the exact
literal conjecture would invalidate the proposed open-problem-resolution
eligibility, without changing the mathematical counterexample.

## Evidence

The formal carrier and sole public result `result : Not claim` are in
`D5/S3/Combinatorics/GeneralizedPetersen/ParityRefutation.lean`.
The proof uses kernel `decide` for the configuration equality, the frozen
evaluation bridge, finite-sum simplification, and exact complex arithmetic.
The matching Scribe definition binds the result to this problem with
`OpenProblemResolutionClaim(Refuted)`.

Primary-source hashes: TeX
`5147f84b91867223e59aa63486af9b4276eadd08dc785fa40ab3c670c80ef004`;
PDF `bae13d4946674f1149b74ef9095d04d9d7ec2d4010dbd8357de52ad88cd066e2`.

## Triage

`theorem`; Tier 1 recent named external conjecture, preregistered in
issue 8619 before proof implementation. The proposed admission is
`open-problem-resolution`, with conservative `proof_shape: bind-only`
and `escape_witness: none`. The computational use is a
`certified-instance` refuting the closed full `claim`. The triangular
prism, its polynomial, and its real-rootedness are classical, including
the claw-free theorem of Chudnovsky and Seymour cited by the source.
No new family, technique, classification, or global priority is claimed.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded screen
cannot exclude every prior resolution. Source-to-Lean fidelity requires
independent comparison with the cited version; the kernel checks the
formal statement and proof, not that prose correspondence. Canonical
admission, frozen membership, and publication are separate obligations;
the authored resolution binding alone does not establish them.
