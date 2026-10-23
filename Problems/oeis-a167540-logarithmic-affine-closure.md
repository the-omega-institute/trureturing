---
slug: oeis-a167540-logarithmic-affine-closure
bibkey: hanna2009affineclosure
doi: null
url: https://oeis.org/A167540
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure
  - D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure
---

# Hanna's full logarithmic arithmetic-subsequence closure

## Problem

> For integers m>0, b>=0, Sum_{n>=0} L(m*n+b) * log(1+x)^n/n! is an integer series whenever Sum_{n>=0} L(n)*log(1+x)^n/n! is an integer series.

The source is the CONJECTURE comment in OEIS A167540. An integer series has
integer ordinary coefficients. The exact formal statement concerns every
characteristic-zero field K, arbitrary L:N->K, every positive natural m and
arbitrary natural b, at every ordinary degree including zero. The only
mathematical premise is integrality of the entire input logarithmic transform.
Integral values of L are derived, with arbitrary L(0). There is no sign,
normalization, support, degree, dilation, shift or analytic restriction.

## Motivation

Arithmetic extraction is a distinct closure operation from pointwise powers.
The original inverse coordinates and classical columns can be reused directly
to settle one complete externally named question, rather than a finite prefix
or a new proof of an existing supplier.

## Gap

The affine-column identity, degreewise finite rearrangement and full-field
transport are proved in the canonically frozen
`HannaLogarithmicAffineClosure.result`. Complete-unit independent review,
the protected-base local gate, exact-head required CI, merged dev delivery
and subsequent dev verification remain outstanding. No counted problem
delivery is claimed.

## Route

Let q_k(N)=k!S(N,k). Original reconstruction supplies a:N->Z with
L(N)=sum_(k<=N) a_k q_k(N). Thus all L(N), including L(0), are embedded
integers as a consequence of the sole premise.

Inclusion-exclusion and exponential rescaling give the rational affine
column EGF as sum_(j<=k) (-1)^(k-j) binomial(k,j) j^b exp(t)^(j^m).
The original exp/log substitution identity identifies its logarithmic
transform with the integer polynomial

`P_(k,m,b)(X) = sum_(j<=k) (-1)^(k-j) binomial(k,j) j^b (1+X)^(j^m)`.

For an arbitrary degree r, log(1+X)^n contributes only for n<=r. Since
m*n+b<=m*r+b, the original T_window identity expands every contributing
value in the common finite range k<=m*r+b. Interchanging these finite sums
gives the coefficient as the integer sum

`sum_(k<=m*r+b) a_k [X^r]P_(k,m,b)`.

Mapping the rational identity into K gives the original full-field result.
The finite bound varies with arbitrary r and imposes no whole-series bound.
Zero indices, 0^0=1, b=0, signed and infinite coordinate sequences are all
included. The output constant is L(b), and b=0 retains arbitrary L(0).

## Falsifier

A refutation would require a characteristic-zero field, arbitrary L whose
entire input transform is integral, a positive m, nonnegative b and an
ordinary output degree with nonintegral coefficient. A failed method bound,
finite-prefix example, altered logarithm or restricted sequence cannot refute
this assertion.

## Evidence

`D5/S1/Recurrence/Algebraic/HannaLogarithmicAffineClosure.lean` contains the
full universal result with standard axiom closure `Classical.choice`,
`Quot.sound`, `propext`. Its premise is inhabited by every integer-coordinate
sequence T(a), since the original transform_T theorem gives exactly the
series with coefficients a; this includes signed and infinitely supported a.
The corresponding Scribe states the same field, sequence, affine parameters,
premise and whole-series conclusion and explains the finite coefficient proof.
The Library note retains source, supplier and bounded-search provenance.

The new result audit and the two newly exposed, directly consumed original
finite-sum helpers remain unfinished under the specific exception
https://github.com/the-omega-institute/trureturing/issues/16582.
The original three audits retain exactly issue 16520; the earlier six API
helper audits retain exactly issue 16571. No exception is a validated audit.

## Triage

`theorem`, Tier 1, admission basis `open-problem-resolution` under
preregistration https://github.com/the-omega-institute/trureturing/issues/16545.
The result resolves the full algebraic implication within the formal system.
Its proof shape is bind-only: classical inclusion-exclusion and original
inverse coordinates supply the identities, and coefficient normalization and
finite summation assemble the conclusion. Each auxiliary theorem is consumed
on the result's live proof path. There is no supplier novelty, separate helper
credit or completed external delivery. The result has independent pre-freeze
source-fidelity and admission approval and canonical freeze; those checks
do not establish complete-unit review, full local admission or required CI.

## ASSUMED-UNVERIFIED

Beyond the Library note's bounded sources and indices, absence of a prior whole
resolution or conflicting owner is unverified. No universal literature-absence
or priority claim is made. Complete-unit independent admission and final
publication checks remain unfinished. No
analytic convergence or positive-characteristic extension is asserted.
