---
slug: englander-a081215-xvii-polynomial-refutation
bibkey: englander2020a081215
doi: null
url: https://oeis.org/A081215/a081215.pdf
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/SelfPowerQuotient
  - D5/S3/Arith/Congruence/SelfPowerResiduePolynomialRefutation
---

# Englander's XVII: the full polynomial-existence assertion is false

## Problem

Physical page 66 of Mathew Englander's *Comments on OEIS A081215* asserts
that for each positive integer $k$ one fixed family of $2k$ degree-$k$
polynomials gives the remainder of the exact quotient $a(n)$ modulo
$n^k+(-1)^k$, selected by $n$ modulo $2k$, for every integer $n>k$.
The formal claim permits arbitrary complex coefficients and therefore
includes real and rational coefficients. All first $2k$ family entries
have degree exactly $k$ and the same family applies simultaneously to all
allowed inputs.

## Motivation

The original unrestricted positive-$k$ assertion includes $k=1,n=2$.
This endpoint distinguishes the claim from the source's already proved
smaller-modulus statement, whose domain starts at $n>2$.

## Gap

[Preregistration #30324](https://github.com/the-omega-institute/trureturing/issues/30324)
records this full existence claim and its bounded qualification. No complete
prior explicit settlement was located in the inspected source, OEIS,
arXiv and named formal-library surfaces. This does not establish worldwide
openness or priority.

## Route

Take $k=1$ and the even residue class. The allowed inputs $n=2,4,6$
have exact quotient values $1,41,5713$. Reducing modulo $n-1$ gives
$0,2,3$. Their second difference is $0-2\cdot2+3=-1$.
Every complex polynomial of degree at most one is affine and its values at
these equally spaced inputs have zero second difference. Direct application
of Mathlib's `Polynomial.eq_X_add_C_of_natDegree_le_one` gives a
contradiction. Thus even unrestricted complex coefficients cannot supply
the required family, and real coefficients cannot do so either.

## Falsifier

A fixed degree-one even-class complex polynomial taking these three values
would falsify the refutation. Choosing a new polynomial for each input,
removing $n=2$, or replacing the assertion by eventual polynomiality changes
the problem and is not an allowed witness.

## Evidence

The exact sequence is imported from `SelfPowerQuotient`; no duplicate
sequence wrapper is introduced. The claim has compiled type `Prop` and
`SelfPowerResiduePolynomialRefutation.result` has the literal type
`Not claim`. Its proof directly computes the three integer quotients and
remainders, applies the degree-one structure theorem and derives the
complex-arithmetic contradiction. The designated literal refutation result
is exempt from four-slot information-escape registration.

## Triage

`theorem`: the full existence assertion is refuted locally. The printed
zero-class formula error is not treated as another independent problem.
No conclusion about a revised $k\ge2$ or eventual assertion is made.
Independent review, canonical freezing and publication are outside this
implementation's authorization; no registered resolution or KPI is asserted.

## ASSUMED-UNVERIFIED

Worldwide priority and complete citation closure are unverified. The
Library entry gives the source pin and citation/license boundary. No
separate permission to redistribute the author's PDF is assumed.
