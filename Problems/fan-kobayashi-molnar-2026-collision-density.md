---
slug: fan-kobayashi-molnar-2026-collision-density
bibkey: fankobayashimolnar2025family
doi: 10.1007/s11139-026-01408-3
url: https://arxiv.org/abs/2511.02106v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Robin/Analytic/LcmPowerLemmaFifteen.lcmPowerF
---

# Fan--Kobayashi--Molnar collision parameters

## Problem

Section 8 of Fan, Kobayashi and Molnar, *A family of analogues to the
Robin criterion*, asks whether the critical-value sets for two distinct
primes can intersect for a real parameter kappa>1. The precise target here
strengthens existence to density: for distinct primes p,q, real
1<alpha<beta, and any natural M, there are kappa in (alpha,beta) and
natural i,j both at least M and at least one such that
F(kappa,p,i)=F(kappa,q,j). F is Definition 4.2, reused without redefinition
as `LcmPowerLemmaFifteen.lcmPowerF`. Issue #30168 preregisters this target.

## Motivation

The critical-value sets determine simultaneous changes in prime
exponents of kappa-colossally abundant numbers. Density answers both
real-parameter existence and existence at arbitrarily large parameters,
while retaining arbitrarily large exponent indices.

## Gap

The target needs an asymptotic coefficient whose ratio varies strictly
with kappa, a positive-tail logarithmic approximation for two distinct
primes, and continuity joining opposite endpoint signs. Neither fixed
integer parameters nor the existence of an isolated numerical collision
supplies density.

## Route

For x>1 set
c(kappa,x)=(x-1)*(x^(kappa-1)-1)/((x^kappa-1)*log(x)). Factoring x^n
from the power bases replaces the exponent n by t=1/x^n. Differentiating
the normalized expression at t=0 gives
F(kappa,x,n)*x^n -> c(kappa,x), for each fixed kappa>1.

For 1<p<q the logarithmic coefficient ratio strictly increases with
kappa. This follows from strict decrease of z/sinh(z) on z>0 and
comparison of the derivatives
s/(exp((kappa-1)*s)-1)-s/(exp(kappa*s)-1), where s=log(x).
The ratio log(p)/log(q) is irrational by unique prime factorization.
Irrational rotations supply i*log(p)-j*log(q) in any open interval with
both natural indices beyond any cutoff. Choose that interval inside
the two endpoint logarithmic coefficient ratios. The two fixed endpoint
limits imply opposite strict signs; continuity gives an interior zero.

## Falsifier

A failure of strict coefficient comparison, positive-tail logarithmic
density, the fixed-parameter limit, or continuity would invalidate the
route. A mismatch between the reused F and Definition 4.2 would invalidate
the interpretation. All hypotheses and the two index lower bounds are
part of the formal target.

## Evidence

The exact statement is
`D5/S3/Arith/Robin/Analytic/LcmPowerCollisionDensity.collision_parameters_dense`.
Its supporting modules are `LcmPowerLeadingTerm`,
`LcmPowerCollisionCoefficient`, `LcmPowerLogLattice`, and
`LcmPowerCollisionCrossing` in the same directory. The source identity is
the existing `Library/ArithSums/fankobayashimolnar2025family.md` note.

## Triage

Lean proved: the real-parameter density assertion with arbitrary
index cutoff, its fixed-parameter leading limit, and the strict
coefficient comparison. Mathematical derivation not formalized: the theory volume's uniform
second-order expansion and parameter-derivative estimates in Lemma 3.1,
and the endpoint values in Lemma 3.2, are separate unformalized clauses.
Countability and measure zero (Theorem 3.4), transcendence (Proposition
3.5), and the conditional integer, three-prime and finite-pair results
(Theorem 3.6) have mathematical derivations in the theory volume but are
not formalized by this target. Undecided: unconditional exclusion or construction
of an integer collision remains undecided.

## ASSUMED-UNVERIFIED

The literature scope is the pinned source and the existing note; this
delivery performs no online search and makes no worldwide priority
claim. The density theorem concerns real parameters and cannot decide
which integer parameters collide. No uniform remainder estimate is
inferred from a fixed-parameter limit.
