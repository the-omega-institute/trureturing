---
slug: chuysurichay-2026-tribonacci-four-bonacci-local-dold
bibkey: chuysurichay2026fibdold
doi: null
url: https://arxiv.org/abs/2609.24544v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/LocalDold/TribonacciFourBonacci
---

# The tribonacci and four-Bonacci local Dold observations

## Problem

Chuysurichay, Jaidee, Panraksa and Ward, *The local Dold congruence for
Fibonacci and Lucas sequences*, arXiv:2609.24544v1, section 4, PDF page 11:

> Another natural problem from the results here is to try and characterize these sets of primes for linear recurrence sequences in general, starting with the intriguing observation that the classical tribonacci sequence (1,1,2,4,...) and 4-bonacci sequence (1,1,1,2,5,...) seem (computationally) to have G_D = ∅.

The quotation normalizes mathematical notation and whitespace. It is an
empirical open observation, without a numbered conjecture. Its positive
sequences are interpreted by their preceding-three and preceding-four
recurrences: T1=T2=1, T3=2, and B1=B2=B3=1, B4=2. Thus
B=(1,1,1,2,5,9,17,33,...).

For a positive natural sequence a and prime p, put b(n)=p^valuation_p(a(n)).
The assertion is that neither sequence has any prime p for which every
positive n divides the integer sum of mu(n/d)b(d) over positive divisors d
of n. Both sequences and every prime are included.

## Motivation

The local Dold condition tests whether arithmetic support of a recurrence
can satisfy orbit-count congruences. Here the recurrence is a coordinate
of an integral invertible action. Its actual inverse coordinate vanishes,
providing a residue class on which that arithmetic support is obstructed.

## Gap

The first-tier recent-source observation and its exact quantifiers were
preregistered in issue 19439. The bounded literature readings collected
on 2026-10-20 cover the target v1 and version history, predecessor
arXiv:2508.11054v2, the Dold survey arXiv:2007.04031v4, Rajs
arXiv:2509.09847v1, and bounded metadata, Crossref and repository searches.
No resolution was found in that scope. The survey's tribonacci trace
sequence has different initial data; a trace-sequence theorem supplies
no identification with the nonlinear p-part sequence here.

The pinned Mathlib supplier SModEq.pow_pow_add_one supplies the quantified
weak congruence lift. Its commutative polynomial-ring formulation can be
evaluated in the noncommutative integer matrix ring. This transfers the existing lift to the integer matrix ring.

## Route

Reduce the integral invertible matrix A modulo p to obtain a positive
period T. Write A^T=I+pC. In integer polynomials, the ideal-power lift of
1+pX evaluated at C gives A^(T*p^j)=I+p^(j+1)D for every natural j.

Set r=pT-1. The inverse coordinate zero implies p divides a(r).
Positive-index positivity gives a(r)>0, so e=valuation_p(a(r)) is at
least one. The residue r is positive, smaller than M=T*p^e, and coprime
to M, including when p divides T. Congruence modulo p^(e+1) preserves
valuation e throughout the positive class r modulo M. Dirichlet gives
prime q in that class above any prescribed H and p^e-1. Since a(1)=1,
the prime-index Mobius sum is exactly p^e-1, strictly between zero and q.

The native companion time at u=1 uses reversed states. Tribonacci uses
(1,1,0), with inverse (1,0,0) and observed coordinate 2. Four-Bonacci uses
(1,1,1,-1), with inverse (1,1,-1,0) and observed coordinate 3. The integer
extension B0=-1 is solely a companion-model value; the natural definition's
unused zero placeholder is zero. All coordinate identifications hold at
every positive index.

## Falsifier

A prime p satisfying all Dold divisibilities for either literal positive
sequence would contradict the assertion. A different four-Bonacci
initialization or a finite list of unsuccessful primes does not test
this assertion. Exact valuation requires modulus p^(e+1), not just p^e.

## Evidence

D5/S3/Arith/LocalDold/TribonacciFourBonacci.result states, for every a equal
to either literal sequence, that goodPrimes(a) is empty and that for every
prime p and every natural H there exists a prime q>H whose integer
Mobius sum S satisfies 0<S<q and q does not divide S. This includes p=2
and H=0. Its hypotheses select the source sequence; they assume neither
prime existence nor valuation classes nor Dold divisibility.

The proof uses
D5/S3/Arith/LocalDold/UnimodularObstruction.unimodular_coordinate_obstruction,
the native finite companion time, and the existing Tribonacci positivity.
The axiom closure is contained in propext, Classical.choice and Quot.sound.

## Triage

### What the settlement shows

Proved, by D5/S3/Arith/LocalDold/TribonacciFourBonacci.result: both printed
sequences have empty local-Dold good-prime sets. At every prime there are
prime-index failures beyond every natural bound, not merely one failing
index.

Proved, by unimodular_coordinate_obstruction: the decisive
conditions are an integral invertible action, positive-index coordinate
identification and positivity, a(1)=1, and the vanishing actual inverse
coordinate. The finite mod-p period need not be coprime to p. No restriction
to odd primes or assertion about positivity at index zero is needed.

Open: characterize good-prime sets for arbitrary linear recurrences, as
requested in the same source paragraph. This proof addresses the two
specified observations. The source's separate Fibonacci and Lucas
characterizations have different initial data; no dependency on these
observations was identified in the inspected source.

## ASSUMED-UNVERIFIED

The bounded literature search does not certify worldwide novelty,
first-publication priority or official uniqueness. The source prints
names and prefixes; the preceding-k recurrence interpretation is stated
explicitly above. No claim concerns another tetranacci convention.
