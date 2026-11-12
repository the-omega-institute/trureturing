---
slug: ovsienko-tabachnikov-first-dual-somos-integrality
bibkey: ovsienko2017dual
doi: 10.1007/s10468-018-9779-3
url: https://arxiv.org/abs/1705.01623v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion.dual_number_lift_preserves_mul_iff_product_rule
---

# First dual non-homogeneous Somos-4 integrality

## Problem

For each pair of positive integers p,q and each c in Z^4, take epsilon^2=0
and A_j=1+c_j epsilon for j=0,1,2,3. The recurrence is

$$A_{n+4}A_n=A_{n+3}^{p}A_{n+1}^{p}+(1+\epsilon)A_{n+2}^{q}.$$

Write its unique forward orbit as A_n=a_n+b_n epsilon. The conjecture is
that all b_n are integers if and only if p=1. The quantifier over c is
outside this equivalence. Positivity, nonvanishing and uniqueness must be
derived from the initial data and recurrence.

## Motivation

Integer dual numbers encode a sequence and its first-order shadows in a
single exchange recurrence. The existing multiplicativity criterion
identifies the product rule for this carrier; it does not establish the
recurrence's integer divisibility or its converse.

## Gap

Corollary 5.2(i) gives the sufficient direction. Its following conjecture
asks for the converse, including the arbitrary initial shadows inherited
from that corollary. The source and indexing normalization are recorded in
the corresponding Library note. The selected full statement is registered
in https://github.com/the-omega-institute/trureturing/issues/29468.

## Route

Work in integer dual numbers modulo the current divisor E. Bézout
identities lift real-part coprimality to units in this quotient. Four
exchange equations give a cleared power identity and the exact criterion
that E divides the next numerator if and only if its real part divides
(2p−2)v, for coefficient 1+v epsilon. No cancellation of epsilon is used.

When the obstruction is zero, strong induction first constructs the next
integer dual term and then propagates coprimality of each four-term real
window. The v=0 case supplies integer real parts for arbitrary p,q; v=1
and p=1 supply integer shadows. Conversely an entirely integer v=1 orbit
would force 2^p+1 to divide 2p−2. For p≥2 this is a positive integer
strictly smaller than 2^p+1, giving a contradiction for each initial tuple.

## Falsifier

A positive p≥2, positive q and integer tuple with an entirely integer
shadow orbit would refute the necessity direction. A p=1 orbit with one
noninteger shadow would refute sufficiency. Finite prefixes can test an
implementation but cannot establish the infinite assertion.

## Evidence

The primary source is §5.4 of the fixed preprint cited by the Library note.
The formal implementation is
`D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.lean`.
It constructs the rational dual orbit, derives positivity and uniqueness,
and includes a faithful real-dual source bridge. Its mathematical status
is determined by Lean and the normal repository admission process.

## Triage

This is a single named source conjecture. The second deformation and the
separate growth conjectures are excluded. Intermediate identities or a
draft pull request do not by themselves certify resolution.

### What the proof establishes

The compiled result
`D5/S1/Recurrence/Invariants/SomosFirstDualIntegrality.result` retains each
integer initial tuple separately and establishes the full infinite
equivalence. The decisive obstruction is divisibility of 2p−2 by 2^p+1;
its failure for p≥2 is independent of q and of the four initial shadows.
The sufficient direction includes q=1. Positivity and uniqueness of the
specified orbit are consequences, rather than additional assumptions.

The source's published p=1 sufficient result is retained. This first-family
theorem makes no conclusion about the second deformation, the independent
growth questions or general weighted quivers. Those questions remain open
in this delivery. Independent source-fidelity review and canonical freezing
are prerequisites for a repository resolution claim.

## ASSUMED-UNVERIFIED

The bounded source screen does not prove exhaustive absence of an earlier
published proof. Source-fidelity review must check the inherited arbitrary
initial tuple and the normalization of the source's inconsistent indices.
No global novelty or priority conclusion is asserted.
