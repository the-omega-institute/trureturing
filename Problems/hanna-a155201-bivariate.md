---
slug: hanna-a155201-bivariate
bibkey: hanna2009a155201
doi: null
url: https://oeis.org/A155201
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility
---

# Hanna A155201: independent-variable exponential integrality

## Problem

For every signed integer $m$, let
$$F_m(x,y)=\exp\left(\sum_{r\ge1}(m^r+y)^r x^r/r\right)
\quad\text{in }\mathbb Q[y][[x]].$$
The exact assertion is $[x^ny^j]F_m\in\mathbb Z$ for every natural $n,j$,
including zero and $j>n$. The variables are independent. No integrality
premise, positivity condition, degree cutoff or analytic convergence
condition is imposed. The source is the first OEIS A155201 COMMENTS clause
quoted in `Library/RecurrenceAlgebraic/hanna2009a155201.md`:

> More generally, it appears that for m integer, exp( Sum_{n>=1} (m^n + y)^n * x^n/n ) is a power series in x and y with integer coefficients.

## Motivation

The frozen original
`D5/S1/Recurrence/Algebraic/HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility`
gives integral coefficients of a series-valued exponential under explicit
prime-power divisibility conditions. Its statement and proof are preserved;
only visibility is exposed at the original declaration. Positive-weight
specialization and triangular coefficient isolation connect that supplier
to Hanna's two independent variables.

## Gap

Scalar integer-valued specializations of $y$ do not establish integrality
of every polynomial coefficient. The full event requires the exact
logarithmic shift, the formal exponential correspondence, all candidate
prime-power divisibility premises and recovery of each original bidegree.
The route below supplies these bridges; it does not assume coefficient
integrality.

## Route

Each logarithmic row has y-degree at most its x-degree, so multiplication
and the finite coefficient formula for the exponential give
$\deg_y[x^n]F_m\le n$. Thus j>n gives zero.

Fix j<=n and set M=n+1. Positive-weight formal evaluation x=T^M,y=T is
coefficientwise locally finite and commutes with the formal exponential.
Use the integral weights $f_r(T)=T^{(M-1)r}(m^r+T)^r$.
The existing series-valued logarithmic sum inserts its own $T^r$:
$$[T^N]\operatorname{logSum}(f)=
\sum_{r=1}^N [T^{N-r}]f_r/r.$$
Consequently this logarithm is exactly the evaluated source logarithm.

For a prime p, the condition at r with p not dividing r has modulus 1.
Otherwise r=pq, q=p^s t, s=v_p(q). The polynomial congruence
$$p^{s+1}\mid (m^{pq}+T)^{pq}-(m^q+T^p)^q$$
follows from Frobenius modulo p and power-divisibility lifting.
The monomial factors in $f_r(T)$ and $f_q(T^p)$ both equal
$T^{(M-1)r}$. Hence $p^{v_p(r)}$ divides their difference in Z[[T]].
The series-valued Dwork supplier gives integer coefficients of
$F_m(T^M,T)$.

At exponent Mn+j only the source bidegree (n,j) can contribute: a<n
would require y-degree greater than a, and a>n already has Ma>Mn+j.
This identifies the desired coefficient with an integer diagonal
coefficient. The n=0 constant and every j>n are included.

## Falsifier

A signed integer $m$ and natural $n,j$ whose actual coefficient in the
stated formal exponential has no integer representative would refute the
exact event. A finite prefix or scalar specialization cannot certify the
unbounded statement. A mismatch in the shifted logarithm or coefficient
isolation would invalidate the proposed bridge to the source event.

## Evidence

The declaration `HannaA155201BivariateIntegrality.result : claim` states the
entire event. Its proof uses the original
`HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility`.
The exact logarithmic shift and exponential bridges are explicit.
All helpers are consumed; the proof is classified bind-only relative to the
existing suppliers. The intended admission basis is external
open-problem-resolution under
https://github.com/the-omega-institute/trureturing/issues/31340 .
The scoped Lean evidence includes the full result and only the standard
axioms Classical.choice, Quot.sound and propext. No numerical experiments
are used.

The official immutable source is OEIS revision #10 at
https://raw.githubusercontent.com/oeis/oeisdata/3b4af0e758dc686db8f67f25863f4c9eb1a8f842/seq/A155/A155201.seq ,
1302 bytes, SHA-256
`8c62bbfc6e19707f161a0f7b6f329d9a7c83e7a515c88fcd948239f806ecf929`.
The source-qualified bounded literature screen is recorded in #31340;
its inspected scalar results do not state full independent-variable
polynomial-coefficient integrality. This is not a global literature census.

## Triage

`theorem` is the problem-pool classification for the exact mathematical
statement, not a machine proof or publication status. The full-result
Scribe carries a typed Proved external-resolution claim naming this
dossier. The mathematical result and its stated source correspondence are
distinct from worldwide priority and the unfinished registration bindings
described below.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are ASSUMED-UNVERIFIED.
The bounded source qualification does not establish either.

The Reg mirrors contain compiled full-telescope realization, equivalence,
variation, sensitivity and observational-dependence proofs for the result,
polynomial congruence, support, extraction and exposed Dwork supplier.
Their lawful enrolled-template applications and original-source bindings
remain unvalidated. The full result has an attempted source selection;
its exact nested coefficient operand reconstruction is not validated.
The other four registrations have no sourceSelection evidence. These
concrete unfinished audit gaps are disclosed in #31340. No
`declared_validated` status is asserted. The unknown continuation residual
proves neither undecidability nor inexhaustibility; registration binding
and required CI remain separate obligations.
