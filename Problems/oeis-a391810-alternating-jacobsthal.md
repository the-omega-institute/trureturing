---
slug: oeis-a391810-alternating-jacobsthal
bibkey: hanna2025a391810
doi: null
url: https://oeis.org/A391810/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/HannaLaurentRowSums
---

# The full alternating Laurent-row formula in A391810

## Problem

OEIS A391810 formula (5), in its original positive-index range, is

$$
-\sum_{k=0}^{\lfloor(n+1)/2\rfloor^2}(-1)^k T(n,k)
=2\operatorname{round}(2^n/3)=2\,\mathrm{A001045}(n),\qquad n\ge1.
$$

Here T(n,k) is the signed coefficient of x to the power -k in the formal
expansion at zero of the literal bilateral sum
`Sum_{j=-oo..oo} x^j*(1-x^j)^(n+j)`. Integer powers with negative exponent
use the Laurent-field inverse. The range includes k=0 and its upper endpoint.
Rounding acts on the exact rational number, with nearest-integer ties toward
positive infinity. A001045 has offset zero and recurrence
`J(0)=0, J(1)=1, J(n+2)=J(n+1)+2*J(n)`.

## Motivation

This exact whole formula is the externally published target registered at
https://github.com/the-omega-institute/trureturing/issues/24532.
The zero row sum, first moment and squared-coefficient questions are separate
events and do not supply this alternating-row conclusion.

## Gap

The qualified official A391810 revision 39 and A001045 revision 1350 fix the
source conventions. Their export fingerprints are given in the cited
library notes. The bounded qualification found no exact or explicitly stronger
supplier in the selected repository delta, reached private declarations,
pinned Mathlib, indexed ownership records, and bounded arXiv/Crossref surfaces.
These negative observations do not certify global priority or solvedness.
SeqFan, complete revision history and unrestricted literature completeness
remain ASSUMED-UNVERIFIED.

## Route

The existing original-Laurent supplier proves that every nonpositive
coefficient is the corresponding coefficient of the integer polynomial
`P_n(y)=-1+Sum_{j=1..n} y^j*(1-y^j)^(n-j)`, and bounds its degree by the
published endpoint. Its bilateral summability and coefficient bridge retain
every integer outer index, including the constant contribution at j=-(n+1).

For n>0, a finite-index shift gives
`P_(n+2)(-1)=P_n(-1)-2^(n+1)`. The recurrence for J gives
`J(n+2)=J(n)+2^n`. Two-step induction from n=1 and n=2 yields
`P_n(-1)=-2*J(n)`. Finite polynomial evaluation and the degree bound then
give the complete alternating signed row sum. Separately, two-step induction
gives `3*J(n)=2^n-(-1)^n`. The parity term places `2^n/3` in the exact
nearest-integer interval for J(n), establishing the rounding equality.
No value of the bilateral series at 1 or -1 is used.

## Falsifier

A positive n at which either equality fails, with the original signed
coefficients and full inclusive bound, falsifies formula (5). A mismatch
between an original Laurent coefficient and the finite polynomial, or a
nonzero nonpositive coefficient beyond the bound, falsifies the corresponding
source bridge or support assertion.

## Evidence

`D5/S3/ArithSums/HannaLaurentAlternatingJacobsthal.full_formula_five` states
the integer alternating/rounding equality, the integer rounding/Jacobsthal
equality, the rational original-Laurent alternating/rounding equality,
the coefficient bridge for every natural k, and vanishing past the bound.
The rational Laurent/Jacobsthal equality follows by casting the second clause.
Its exact declaration is the single terminal result, with no companion alias.

The module retains the offset-zero definition and six private consumed
helpers. `polynomial_at_neg_one_skip` and `alternating_coefficient_bridge`
are bind-only helpers consumed by `polynomial_at_neg_one` and
`full_formula_five`, respectively. The closed-form and positive-index
polynomial inductions provide content on the terminal live proof path.
Admission is the preregistered exact external open-problem resolution;
classical Jacobsthal identities carry no independent novelty claim.

## Triage

The statement is an explicit external conjecture with a universal positive-n
endpoint. The finite polynomial at n=0 equals -1 whereas J(0)=0, so this
argument does not extend the row identity to zero. Formal source fidelity,
registration, freezing and delivered publication are distinct obligations.

## ASSUMED-UNVERIFIED

Global literature priority and solvedness outside the bounded qualification
remain unverified. This dossier makes no delivery or KPI claim and does not
settle any other A391810 formula.

The terminal theorem's four-slot information registration is unfinished.
For the signed row-entry observation its remaining local dependence goal is
`-1 != -(Polynomial.coeff 1 1)+1`, comparing entries zero and one in row one.
The complete-family zero intervention, full-telescope equivalence and
source selection have no accepted current binding evidence; no compiled
Reg mirror or `declared_validated` status is claimed. This local proof gap
does not establish a limitation of the registration producer.
