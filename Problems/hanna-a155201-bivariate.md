---
slug: hanna-a155201-bivariate
bibkey: hanna2009a155201
doi: null
url: https://oeis.org/A155201
triage: open
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.result
---

# Hanna A155201: independent-variable exponential integrality

For every signed integer $m$, let
$$F_m(x,y)=\exp\left(\sum_{r\ge1}(m^r+y)^r x^r/r\right)
\quad\text{in }\mathbb Q[y][[x]].$$
The exact assertion is $[x^ny^j]F_m\in\mathbb Z$ for every natural $n,j$.
The variables are independent. No integrality premise or analytic condition
is imposed. The source is the first OEIS A155201 COMMENTS clause quoted in
`Library/RecurrenceAlgebraic/hanna2009a155201.md`.

## Argument

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

## Source and verification boundary

The declaration `HannaA155201BivariateIntegrality.result : claim` states the
entire event. Its proof uses the original
`HannaSelfSubstitutionIntegrality.exp_logSum_integral_of_divisibility`
with visibility exposed at that declaration, preserving its statement and
proof. The exact logarithmic shift and exponential bridges are explicit.
All helpers are consumed; the proof is classified bind-only relative to the
existing suppliers. The intended admission basis is external
open-problem-resolution under #31340, pending independent approval.

The current scoped Lean build and report include the full result and its
standard axiom closure: Classical.choice, Quot.sound and propext.
The original supplier has a visibility-only canonical ledger repin.
The new result has no frozen-state registration.

The Reg mirrors contain compiled full-telescope realization, equivalence,
variation, sensitivity and observational-dependence proofs for the result,
polynomial congruence, support, extraction and exposed Dwork supplier.
The full result has an attempted source selection; its exact nested
coefficient operand reconstruction is not validated. The other four
registrations have no sourceSelection evidence. These named binding gaps
belong with the unfinished audit in #31340; external issue updates are not
part of this source delivery. No declared_validated status is asserted.

Independent pre-freeze approval, canonical first freezing, and publication
are outstanding. Reg binding and required CI are separate obligations;
no declared_validated, merged delivery, worldwide priority or published
settlement is asserted here. No numerical experiments are used.
