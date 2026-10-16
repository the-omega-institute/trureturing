---
slug: oeis-a167138-logarithmic-power-closure
bibkey: hanna2009logarithmicclosure
doi: null
url: https://oeis.org/A167138
triage: theorem
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

## Motivation

The question asks whether integer ordinary coefficients in logarithmic
coordinates survive every positive pointwise power of the EGF coefficient
sequence. The three OEIS entries give examples of the same universal closure
question; settling it requires the arbitrary sequence, rather than only their
square examples or a finite coefficient window.

## Gap

The known fixed-column Hadamard EGF identity supplies products of Stirling
columns. The whole question requires reconstruction from the original
integrality premise, extension to arbitrary sequences by finite contributions
at each degree, and transport back to the original characteristic-zero field.
Integrality of L must be derived, not added as an assumption.

## Route

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

## Falsifier

A counterexample to the original assertion would be a characteristic-zero
field K, a sequence L satisfying the original integral-series premise, a
positive exponent m and an ordinary degree r whose transformed coefficient
lies outside the canonical integer image. Degree zero and arbitrary L(0)
remain part of this criterion. A fixed-column identity alone, a finite
coefficient check or a proof requiring integral L as an extra premise would
not settle the stated question.

## Evidence

Preregistration: https://github.com/the-omega-institute/trureturing/issues/16500.
The Library note records immutable primary hashes, the bounded exact-question
literature/ownership searches and their access gaps. The finite column supplier
is Boyadzhiev–Frontczak, Corollary 3.1, DOI 10.47443/ejm.2022.024. It and the
adapted exp/log inverses are known results, with attribution and the complete
Apache license retained for the inverse leaves. The exact arbitrary-field
result and its supplier dependencies have kernel-checked statements with only
Classical.choice, Quot.sound and propext in their accepted axiom closure.
No proof novelty or global absence is claimed.

## Triage

Theorem: the complete original assertion is proved over every
characteristic-zero field, with arbitrary L, every positive pointwise power
and every ordinary degree including zero. The result is canonically frozen;
this mathematical state does not establish complete admission or delivery.
The admission basis is `open-problem-resolution` for issue 16500. The main
module has five authored definitions, eighteen authored bind-only theorems
and two compiler-generated congruence declarations; its known suppliers do
not supply a separate new-result or escape claim. A167138, A167139 and
A167141 are one question, eligible for at most one eventual count.

Proved mechanism: the integral logarithmic-coordinate series form a class
closed under pointwise multiplication of EGF coefficient sequences, and
therefore under every positive pointwise power. The proof applies to signed,
unbounded and infinitely supported coefficients over every characteristic-zero
field. Every rearrangement is finite in each ordinary degree. It makes no
analytic-convergence assertion, positive-characteristic claim, minimal-support
claim or assertion of novelty of the supplier identities. No additional
source-dependent consequence is claimed.

Unfinished audit: all three source-owner Reg mirrors remain
`declared_unresolved`, with null certificates and
`IE-C050/unclassified_form/source.selection_missing`. Their equivalence,
variation, sensitivity and dependence proofs do not supply the missing raw
source-selection coordinates/observations, inverse packing and full
original-statement reconstruction. The unfinished audit is disclosed at
https://github.com/the-omega-institute/trureturing/issues/16520; that exception
waives no other delivery duty.

The six exposed helper audits remain unfinished at
https://github.com/the-omega-institute/trureturing/issues/16571.
The directly consumed `coeff_transform` and `T_window` helper audits have
their separate scope at
https://github.com/the-omega-institute/trureturing/issues/16582.
These scopes supply no validated registration and do not change the original
three-target scope at issue 16520.

Unmet delivery duties: complete canonical local admission, the mandatory
independent publication review triplet, exact-current-head required CI,
MERGED status and subsequent dev verification remain necessary. The unit is
an honest draft with no completed admission or external-problem count claimed.

## ASSUMED-UNVERIFIED

The bounded literature and ownership searches do not certify worldwide
absence of a prior settlement or establish priority. SeqFan archive access
failed, some general search services rejected or rate-limited requests, and
the related log/integer search inspected the first fifty of fifty-three hits.
The source attribution does not independently establish the conjecture's
insertion date. The characteristic-zero field interpretation makes the
source's implicit ambient field explicit; positive characteristic and
analytic convergence are outside the result. Unfinished audit and delivery
evidence have the limits stated in Triage.
