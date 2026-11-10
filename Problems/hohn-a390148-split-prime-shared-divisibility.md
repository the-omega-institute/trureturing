---
slug: hohn-a390148-split-prime-shared-divisibility
bibkey: hohn2025a390148
doi: null
url: https://oeis.org/A390148
triage: theorem
motivation_gids:
  - D5/S3/Arith/Descartes/SplitPrimeSphereRadii.result
---

# Hohn's split-prime shared-divisibility assertion

## Problem

Charles L. Hohn, OEIS A390148, revision 23, states:

> For each term in a quadruple that is divisible by a positive power of prime p = 1 mod 3, 1 or 2 of the other terms are divisible by at least the same positive power of p.

For every function r:Fin 4 -> Nat whose four values are positive and have common gcd 1, assume (sum_i 1/r(i))^2 = 3*sum_i (1/r(i))^2 over Q. For every prime p with p mod 3 = 1, every positive natural integer k, and every index i:Fin 4 such that p^k divides r(i), the cardinality of the set of indices j:Fin 4 with j != i and p^k dividing r(j) is either 1 or 2. This quantifies all positive powers, allows repeated and unsorted radii, and assumes only common primitivity, not pairwise coprimality. There is no finite size, algorithmic, resource, Lean or verification condition. The single event is this entire source split-prime shared-divisibility assertion, separate from the p=3 valuation clause, the p mod 3 = 2 even-valuation clause, repetition counts and chains.

## Motivation

The assertion controls simultaneous divisibility of coordinates in the
coefficient-three spherical Descartes equation. It constrains every positive
prime-power threshold rather than only maximal valuations.

## Gap

This is a tier-one externally stated conjecture, preregistered in issue #28788.
The pinned primary locator and bounded supplier search are in the corresponding
Library note. The source states an unbounded conjecture. No global absence of
earlier proofs or mathematical priority is claimed.

## Route

Use the canonical positive integral curvatures b(i)=L/r(i), with L the lcm.
Their common gcd is one and they satisfy the integral coefficient-three
equation. For any coordinate i, some other curvature is nonzero modulo p:
otherwise primitivity makes b(i) nonzero and the equation gives
2b(i)^2=0 modulo p. This contradicts primality and p being odd.

The product identities give v_p(b(a))+v_p(r(a))=v_p(L). The other unit
curvature therefore supplies a radius with valuation at least v_p(r(i)).
Common gcd one excludes all four radii being divisible by p^k when k>0.
At least one and at most two other coordinates satisfy the threshold.

## Triage

The Lean endpoint proves the complete split-prime assertion. Independent
pre-freeze review approved the retained mathematical sources. Canonical
owner identity migration, endpoint freezing and publication remain pending.
The proof mechanism uses only oddness in its modular step;
no additional all-prime endpoint is asserted here. The inert-prime
even-valuation condition, repetition counts and chains remain unresolved by
this result. Their distinct source statements require separate qualification.

## Audit boundary

The endpoint's source-bound registration compiles, but its native state is
`declared_unresolved`, with a null certificate and
`IE-C050 ClosedTruthReadout reason=unclassified_form rule=source.state_binder`.
The original state binder r precedes the selected parameters p, k and i;
the repeated cardinality also needs accepted occurrence binding. The exact
unfinished endpoint audit is disclosed in
[issue #28788](https://github.com/the-omega-institute/trureturing/issues/28788#issuecomment-6763920715).

The newly public owner lemmas
`PrimitiveSphereRadii.curvature_pos`,
`PrimitiveSphereRadii.curvature_mul_radius`,
`PrimitiveSphereRadii.curvature_primitive` and
`PrimitiveSphereRadii.curvature_equation` also have unfinished audits under
the same [issue](https://github.com/the-omega-institute/trureturing/issues/28788#issuecomment-6764674370).
The dependent-family template can express their complete source laws;
this alone supplies no validated registration. For the first
two, the original state r precedes the index i needed by the readout.
The latter two still need complete family intervention, sensitivity,
observational-dependence and accepted source-occurrence evidence.
No owner registration or `declared_validated` certificate is claimed.
The exposed definitions `commonMultiple` and `curvature` are not theorem
audit targets. These audit boundaries do not weaken the source assertion
or settle the separate source clauses.
