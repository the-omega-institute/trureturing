---
slug: oeis-a167138-logarithmic-power-closure
bibkey: hanna2009logarithmicclosure
doi: null
url: https://oeis.org/A167138
triage: candidate
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
---

# Hanna's universal logarithmic integer-series closure

## Problem

> Conjecture: For all integers m > 0, Sum_{n>=0} L(n)^m * log(1+x)^n/n! is an integer series whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series.

A167138, A167139 and A167141 repeat this one general Hanna question.
An integer series has integer ordinary coefficients. Let K be any
characteristic-zero field and L any function from natural numbers to K.
Put E_L(t)=sum L(n)t^n/n! and ell(X)=log(1+X). The exact conclusion is
integrality of E_(L^m)(ell(X)) for every positive integer m whenever
E_L(ell(X)) is integral, at every degree including zero. The natural
positive exponent in Lean is the equivalent representation of a positive
integer exponent. L(0) is arbitrary. No extra integral-L assumption,
analytic convergence, finite support or degree/power bound is introduced.

## Mechanism

Write q_i(n)=i!S(n,i) and T(a,n)=sum_(i<=n) a_i q_i(n).
The original premise and the compositional inverse exp(t)-1 reconstruct
L(n) as the canonical integer image of T(a,n); integrality of L is a
consequence. Rational reconstruction is transported through the canonical
rational algebra map into the original field.

The integer series
P_ij(X)=sum_(s<=i) (-1)^(i-s) binomial(i,s) ((1+X)^s-1)^j
is the logarithmic transform of q_i q_j. The fixed-column identity is the
factorial-scaled formal version of Boyadzhiev–Frontczak Corollary 3.1.
For degree r, q_i(n) vanishes when i>n and ell(X)^n vanishes in degree r
when n>r. Hence the output coefficient for T(a)T(b) is the finite integer
sum sum_(i,j<=r) a_i b_j [X^r]P_ij. Binary closure and induction give all
positive powers. At degree zero this retains precisely L(0)^m.

## Sources and limits

Preregistration: https://github.com/the-omega-institute/trureturing/issues/16500.
The Library note records immutable primary hashes, the bounded exact-question
literature/ownership searches and their access gaps. The finite column supplier
and the adapted licensed exp/log inverses are known results, with attribution
and the complete Apache license. No proof novelty or global absence is claimed.

## Triage

The whole original assertion is the only settlement target. The admission
basis is `open-problem-resolution` for issue 16500; this is not a separate
new-result claim for its classical suppliers. The mathematical draft remains
unfrozen until an independent fidelity/admission review and canonical delivery.
The complete arbitrary-field result is kernel-checked. The source-owner Reg
mirrors retain equivalence, variation, sensitivity and dependence proofs, but
their raw source selections remain unfinished. The concrete binding and scoped
governance consumption gaps are recorded in
https://github.com/the-omega-institute/trureturing/issues/16520.
This is neither completed admission nor a counted external-problem delivery.

## What the settlement shows

The mechanism identifies the integral logarithmic-coordinate series as a
class closed under pointwise multiplication of EGF coefficient sequences,
and therefore under every positive pointwise power. It applies to signed,
unbounded and infinitely supported coefficients over every characteristic-zero
field. Every rearrangement is finite in each ordinary degree. It makes no
analytic-convergence assertion, positive-characteristic claim, minimal-support
claim or assertion of novelty of the supplier identities.
