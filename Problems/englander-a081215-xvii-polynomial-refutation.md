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

[Physical page 66](https://oeis.org/A081215/a081215.pdf#page=66) of Mathew
Englander's *Comments on OEIS A081215* asserts
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

`theorem`: `SelfPowerResiduePolynomialRefutation.result : Not claim`
refutes the complete fixed-family existence assertion over complex
coefficients. The canonical Scribe resolution claim binds this endpoint to
`englander-a081215-xvii-polynomial-refutation` with kind `Refuted`.

**What the settlement shows.** The original positive-$k$ domain permits
$k=1$ and all three inputs $n=2,4,6$. Their even-class remainders
$0,2,3$ cannot come from one degree-one complex polynomial. Thus the full
assertion fails even when its coefficients range over all of $\mathbb C$;
restricting to real or rational coefficients cannot restore it. No input
or quantifier in the original claim is removed.

The source's Theorem III, displayed on
[physical page 1](https://oeis.org/A081215/a081215.pdf#page=1) and recalled on
physical page 66, states $a(n)\bmod(n-1)=\lfloor n/2\rfloor$ for $n>2$.
Its narrower domain excludes the offending endpoint $n=2$, where the
remainder is zero and $\lfloor n/2\rfloor=1$. That literature result is
not contradicted by this refutation and is not a new formalization here.
A revised eventual assertion or a $k\ge2$ assertion remains open. Effects
on other source arguments are unverified; no further numbered problem is
settled. The separate printed zero-class formula error is not a third
problem, and XX remains outside scope.

## ASSUMED-UNVERIFIED

Worldwide priority and complete citation closure are unverified. The
Library entry gives the source pin and citation/license boundary. No
separate permission to redistribute the author's PDF is assumed.
