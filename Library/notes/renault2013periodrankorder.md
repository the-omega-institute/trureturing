---
bibkey: renault2013periodrankorder
authors: Marc Renault
year: 2013
title: The Period, Rank, and Order of the (a,b)-Fibonacci Sequence Mod m
doi: 10.4169/math.mag.86.5.372
claim: Theorems 1-2 give least-common-multiple period and rank laws and prime-power lifting with the actual initial delay retained; they do not assume absence of WSS primes.
strata_touched: []
license: citation-only
triage: anchor
---

# Golden-clock sampling and the original prime-power delay

## Primary source and exact role

Marc Renault, *The Period, Rank, and Order of the (a,b)-Fibonacci Sequence
Mod m*, Mathematics Magazine 86 (2013), 372-380.
https://doi.org/10.4169/math.mag.86.5.372
Author-hosted published text:
https://webspace.ship.edu/msrenault/fibonacci/RenaultPeriodRankOrderMathMag.pdf

The Preliminaries on printed pages 373-374 identify matrix order with
pair period and scalar return with the zero rank. Theorem 1 on page 374
proves the least-common-multiple laws. Theorem 2 on page 376 retains the
initial prime-power plateau before subsequent lifts multiply the period
by p. These are the classical inputs retained from the earlier source
note in closed PR8343. Its earlier source inspection is not represented
as a new literature review in this transfer.

For the standard sequence, the two common Fibonacci matrices are conjugate
by the swap of their coordinates. This preserves every residue order.
The exact real eigenpairs recorded by the existing FibonacciEigen Scribe
identify the same integer substitution, but do not decide its p-adic lift.
The full golden-clock matrix at layer L is Q^(L+2); the scalar floor map
and real fractional-part observation are kept distinct from the matrix
modulo a prime square.

## Mathematical consumer in the existing WSS owner

`Problems/wall-sun-sun-golden-unit-lift.md`, PCL.1-PCL.7, proves the
following ordinary specializations for the original recurrence:

- With stride s and external-period valuation beta_p, the extra exponent
  is max(0,a_p-h_p-max(beta_p,v_p(s))). Coupling and stride delays combine
  by their maximum. The simultaneous square lift of a squarefree modulus
  sees exactly the non-WSS sinks in its increasing prime-period graph.
- The actual quotient F_(p^b)/F_(p^(b-1)) supplies larger primes of exact
  rank p^b and period 4p^b. This constructs arbitrarily deep auxiliary
  period masking, not new original WSS depths. The explicit cofactor
  F_(p^b) gives the same period without requiring its factorization.
- The two ternary families C_j=L_(3^j)^2+1 and B_j=L_(3^j)^2+3 have exact
  native block-power periods. Lemma PCL7A includes their rank and actual
  valuation proofs locally; no unmerged TBN or DCE appendix is required.
- Their base periods contain only two and three, absent from their prime
  supports. Native multiplicities nevertheless hide h_p. Replacing a
  block product by its radical makes the square-lift ratio exactly the
  product of simple factors. That radical still needs independent control.
- The block products have an exact K+1-step period-iteration trajectory to
  24, whereas the transient exponent of the largest prime P is
  max(a-n*h_P,0). A common terminal fixed point does not decide WSS.

The B-block period formula also occurred in the GPC continuation of
PR8343. It is retained as an input-compatible specialization and is not
recounted as another discovery. PCL supplies its proof and does not rely
on that closed PR's reciprocity or spectral appendices. Independent
priority of the block and masking specializations is not claimed.

## Other classical sources retained from the prepared PCL package

B. Benfield and O. Lippard, *Fixed Points of K-Fibonacci Sequences*,
arXiv:2404.08194v2, Theorems 2.1-2.2, 2.6 and 2.11:
https://arxiv.org/html/2404.08194v2
The source attributes ordinary Fibonacci fixed-point classification and
convergence to Fulton-Morris (1969). PCL proves the displayed special
trajectories, not a new general fixed-point theorem. The separate
conjecture about generalized (a,-1) sequences is not used.

T. Ross, Z. Shen and T. Cai, *The p-adic Valuations of Mobius Duals of
Lucas Sequences*, arXiv:2512.03481v1, Proposition 3.2 and the classical
attribution in Theorem 3.3:
https://arxiv.org/html/2512.03481v1
The regular-sequence valuation input retains h_p and credits classical
Lucas theory. It does not assert a simple primitive factor or a WSS example.

## Formal and arithmetic boundary

The existing `Blueprint/D5/S1/Scale/FibonacciEigen.scribe.cs` links this
note as ordinary downstream context for the same Fibonacci substitution.
Its formal declaration and formula are unchanged. This reference does not
add the period results to the Lean theorem. No new Lean source, compiler
pass, kernel certification, WSS example or new WSS prime-family decision
is claimed. The remaining obligation is an independent restriction on the
original initial depths or on the simple-factor support.
