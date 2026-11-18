---
slug: oeis-a401714-unitary-squarefree-divisor-sum
bibkey: karttunen2026a401714
doi: null
url: https://github.com/oeis/oeisdata/blob/24e9613f999e4d1e98e6d8a4c2b6ae0124d79ed8/seq/A401/A401714.seq
triage: theorem
motivation_gids:
  - D5/S3/Arith/EulerFormDivisorSum
---

# Radical quotient and the joint divisor-sum inequality

## Problem

> %F A401714 a(n) <= A401715(n), conjectured.

The reciprocal `%F A401715 a(n) >= A401714(n), conjectured.` is the same
assertion. For every positive integer N, define rad(N) as the product of
its distinct prime factors, q(N) as its least nondividing prime,
U(N)=sum of d over positive divisors with gcd(d,N/d)=1, and S(N)=sum of d
over positive squarefree divisors. The assertion is
N/rad(N)<q(N) implies 2N<=U(N)+S(N). Both sums include one. There is no
bound on N, parity restriction or support-size restriction.

## Motivation

This is a first-tier recent OEIS conjecture, authored by Antti Karttunen
on November 6, 2026. The frozen Euler-form divisor-sum module supplies
the actual sums and their prime-product interface, but its strict
inequality concerns a different family and the opposite direction.
The complete original records are identified by the linked Library note.

## Gap

The two original entries retain the conjecture and contain no proof.
The necessary source-to-formal correspondence is the radical quotient,
the least missing prime, and the two actual sums. A finite table or a
proof for only some support sizes cannot establish the assertion.
Literature absence beyond the inspected sources and independent
certification remain unverified.

## Route

Put m=N/rad(N). If m<q(N), every prime at most m divides N. Complete
prime-power choices give U(N)=product(p^v_p(N)+1), while the squarefree
sum is product(p+1). After division by N, mandatory small primes give
a lower bound for the joint normalized sum.

For 1<=m<=999, retain the factors 1+1/p^(v_p(m)+1); ten private consumed
kernel certificates establish the required rational bound. For m>=1000,
the product of 1+1/p over primes p<=m not dividing m is at least two.
The latter estimate splits by whether m has at most nine prime divisors.
Small supports are controlled by the first nine primes and an exact
product comparison at 1000. Large supports use a harmonic-sum lower
bound, a support-cardinality upper bound and logarithmic growth.
These ranges cover every positive m, with no cutoff on N.

## Falsifier

A positive N satisfying N/rad(N)<q(N) and U(N)+S(N)<2N would refute the
source assertion. Excluding the divisor one, replacing an actual sum by
an assumed product, or adding a boundedness or parity hypothesis would
change the problem rather than settle it.

## Evidence

`D5/S3/Arith/Divisors/KarttunenA401714.result` states the implication for
every natural N with 0<N, using the existing actual divisor sums.
`leastMissingPrime` is defined by `Nat.find` on primes not dividing N;
existence follows from a prime greater than N. The result derives
mandatory support from the strict least-prime comparison and invokes
`UnitaryProductBridge.unitary_squarefree_ge_twice_of_support`.

The compiled implementation is evidence for the exact mathematical
statement. The Scribe resolution binding names this single assertion;
it does not certify source fidelity, literature priority or completion
of the repository's independent review and freezing duties.

## Triage

The proof's decisive condition is that every prime at most the radical
quotient divides N. For positive N this condition is equivalent to
m<q(N): a missing prime at most m contradicts the condition, and any
prime at most m below q(N) must divide N. This equivalence is an
explanatory consequence of the least-prime definition, not an additional
delivered Lean declaration.

The source's converse is not asserted. Its recorded N=240 distinction
shows why equality of the two characteristic functions is a different
claim. Extending the estimates to other weights or divisor sums remains
unresolved. The two reciprocal conjecture lines count as one problem.

## ASSUMED-UNVERIFIED

Independent fidelity and proof-shape review, the independent review
triplet, canonical freezing and the exposed Euler-form declarations'
canonical repin remain outstanding. The four-slot registrations for all
eight new public theorems remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/31155;
no `declared_validated` registration is claimed. Published-source
qualification is bounded as specified in the Library note. No global
priority, publication or independently certified resolution is claimed.
