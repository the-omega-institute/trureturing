---
slug: oeis-a388986-euler-form-divisor-sum
bibkey: oeis2026a388986
doi: null
url: https://oeis.org/A388986
triage: theorem
motivation_gids:
  - D5/S3/Arith/EulerFormDivisorSum
---

# The A388986 Euler-form inclusion question

## Problem

Does every number in A228058 belong to A388986? Explicitly, let p be prime,
p congruent to 1 modulo 4, a a natural number, and r an odd integer greater
than one with gcd(p,r)=1. Put N=p^(4a+1)r^2. The question asks whether the sum
of the unitary divisors of N plus the sum of its squarefree divisors is
strictly less than 2N.

## Motivation

This is a first-tier recent OEIS question. A388986 revision 36, read on
September 9, 2026, still asks whether A228058 is a subsequence. The Euler
form describes candidates for odd perfect numbers, but this question does
not assert the existence or nonexistence of odd perfect numbers.

## Gap

The complete main entry and its 15 direct A references contain no proof of
the inclusion. A389079 and A389219 repeat it as a conjecture. The known
prime-product formulas for each divisor sum do not alone supply the joint
strict estimate. Finch's Unitarism and Infinitarism and Trudgian's The sum
of the unitary divisor function were also checked; their results concern
parametrizations and asymptotic estimates, not this Euler-form inequality.

## Route

Parametrize a unitary divisor by its prime support: coprimality forces its
exponents to be the full exponents in N. Injecting these supports into the
powerset bounds the unitary sum by the product of q^e+1. Mathlib's squarefree
divisor powerset identity gives the other sum as the product of q+1.

Divide by N>0. A finite minimum-induction argument bounds the product of
1+1/q^2 over integers q>=b>1 by b/(b-1). For the nonempty prime support of r,
split into no 3, only 3, and 3 with another prime. These cases bound the sum
of the two normalized support products strictly below 5/3. The distinguished
prime p>=5 contributes at most 6/5 to either product, giving the strict
bound below 2. Larger exponents only decrease the normalized factors.

## Falsifier

An admissible triple p,a,r whose actual two divisor sums add to at least 2N
would contradict the formal statement. The excluded case p=5,a=0,r=1 gives
N=5 and 6+6>10, so nonempty remaining support is essential.

## Evidence

The Lean theorem is D5/S3/Arith/EulerFormDivisorSum.euler_form_lt. The
definitions unitarySum and squarefreeSum use filtered Nat.divisors directly.
There is no finite cutoff in the statement or proof.

The continuation worker independently checked all positive N through 10^6:
both divisor-sieve sums agree with the prime-product formulas everywhere;
all 12,941 Euler-form instances pass. At p=5,a=0,r=3, N=45 and 60+24<90.
The largest observed ratio is 28/15, attained at 45. This enumeration is a
diagnostic check and is not used by the Lean proof.

## Triage

Theorem: the exact A228058 inclusion question is answered affirmatively.
The separate 2026 prime-factorization-subset conjecture on the same OEIS
page is outside this result.

## ASSUMED-UNVERIFIED

Publication priority and absence of unindexed proofs are not established.
The source-to-formal identification is documentary; the Lean kernel checks
the explicit filtered sums and all quantified hypotheses. The continuation
worker rechecked the inherited proofs and numerical claims; it does not
claim independent multi-model review or verification by the caller.
