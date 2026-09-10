---
slug: oeis-a338193-egf-coefficients
bibkey: oeis2024a338193
doi: null
url: https://oeis.org/A338193
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/SchroderIntegralEGF
---

# The EGF coefficients of A338193 and Kurkov's recurrence

## Problem

The October 26, 2024 conjecture by Mikhail Kurkov in OEIS A338193 asserts
that a(n)=f(0,n-1) for every positive n. Here a(n)=n! times coefficient n
of the rational formal series satisfying A(0)=1 and
A=1+Integral ((x/A)' / (x/A^2)') dx, with integral constant zero.
The independent natural-valued recurrence has f(j,0)=1,
f(0,m+1)=f(0,m)+(m+1)f(1,m), and
f(j+1,m+1)=f(j,m+1)+(m+1)(f(j+1,m)+f(j+2,m)).

## Motivation

The equality connects the integral equation to a recurrence entirely in
natural numbers. In particular it explains integrality of the EGF
coefficients at every index, beyond any finite coefficient calculation.

## Gap

The source prints the equality as a conjecture without a proof. Its separate
one-dimensional recurrence does not supply the connection to the two-index
recurrence. The formal integral equation must also determine a unique series.

## Route

Let F(j) be the EGF of row j and let R be Mathlib's large Schroeder series,
which satisfies R=1+xR+xR^2. Induction first on degree and then on row index
proves F(j)=F(0)R^j. The boundary yields B'=F(0) for B=F(0)(1-xR).
The quadratic for R implies the original equation for B. Clearing units
in that equation identifies its constant-one branch with (1-xR)A'=A.
Induction on coefficients proves uniqueness, hence B=A and the conjecture.

## Falsifier

A positive n with different exact rational values of n! times coefficient n
of the specified A and f(0,n-1) would contradict the conjecture. A formal
solution with constant coefficient one distinct from B would contradict the
uniqueness theorem. Finite agreement alone would establish neither result.

## Evidence

The module `D5/S1/Recurrence/Algebraic/SchroderIntegralEGF.lean` constructs
the recurrence and proves `original_exists_unique`, `A_original`, and
`egf_coeff_eq_f`. Its definition of A selects solely by the original equation
and initial value. The implementation report records the library searches,
all-degree proof, kernel checks, and freeze receipt.

## Triage

`theorem`. This dossier concerns exactly the coefficient identity for positive
indices. The proof is over rational formal series; analytic convergence,
asymptotics, and historical priority are not asserted.

## ASSUMED-UNVERIFIED

The worker fetched and read the main internal entry. The user's reading of
six one-hop sources is supplied due diligence, not a claim that this worker
opened those pages. No claim of absence of all prior proofs is made.
