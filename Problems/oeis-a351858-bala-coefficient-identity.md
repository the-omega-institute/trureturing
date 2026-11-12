---
slug: oeis-a351858-bala-coefficient-identity
bibkey: bala2022a351858
doi: null
url: https://oeis.org/A351858
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result
---

# Bala's finite-binomial coefficient identity for OEIS A351858

## Problem

OEIS A351858, NAME field, revision 31 (unpaginated), defines

> a(n) = [x^n] (1 + x + x^2)^(3*n)/(1 + x)^(2*n).

Peter Bala's FORMULA entry states

> Conjecture: a(n) = Sum_{k = 0..floor(n/2)} C(3*n,k)*C(n-k,k).

The attribution is Peter Bala, Feb 27 2022. The complete assertion is

$$
\forall n\in\mathbb N,\qquad
[X^n]\left((1+X+X^2)^{3n}((1+X)^{2n})^{-1}\right)
=\left(\sum_{k=0}^{\lfloor n/2\rfloor}
\binom{3n}{k}\binom{n-k}{k}\right)_{\mathbb Q}.
$$

The left side is a coefficient in the formal power-series ring
$\mathbb Q[[X]]$. The inverse is the formal multiplicative inverse at zero:
the denominator has constant coefficient one. The sum is formed in the
naturals using ordinary binomial coefficients and then cast as a whole to
the rationals. Both endpoints are included. Subtraction and division in
the indices are natural subtraction and floor division. All natural
indices, including zero and one, are quantified; the OEIS offset `0,3`
imposes no lower bound of three. There is no positivity, primality,
eventual-index, convergence or congruence premise.

## Motivation

The finite positive binomial sum gives an explicit expression for the
coefficient of an independently defined rational formal series. It
connects coefficient extraction after a fractional-linear substitution to
ordinary binomial coefficients without defining the sequence by its
proposed answer.

## Gap

The source snapshot labels the finite identity a conjecture. The bounded
source and prior readings in the cited Library note and
[preregistration #26252](https://github.com/the-omega-institute/trureturing/issues/26252)
did not identify an existing whole proof. This is a not-found-in-searched-
scope result; it does not certify worldwide openness or priority.
The separate supercongruence in the same sequence entry is a different
assertion and is outside this problem.

## Route

For positive $n$, set $X=T/(1-T)$ and multiply the substituted series by
$(1-T)^{n-1}$. The degree-$n$ coefficient is unchanged. To see this, expand
an arbitrary source series into monomials. The weighted image of its
degree-$j$ term is $T^j(1-T)^{n-1-j}$ for $j<n$, which has degree at most
$n-1$; the degree-$n$ term contributes exactly its original coefficient,
and higher terms have order greater than $n$.

For this source, the weighted transform equals

$$
\frac{(1+T^2/(1-T))^{3n}}{1-T}.
$$

Binomial expansion gives terms
$\binom{3n}{k}T^{2k}(1-T)^{-k-1}$. Their degree-$n$ coefficients are
$\binom{3n}{k}\binom{n-k}{k}$ when $2k\le n$, and zero otherwise.
Thus precisely the inclusive range through $\lfloor n/2\rfloor$
contributes. At $n=0$ both sides are one; $n=1$ is included in the positive
case. Casting the natural sum then gives the rational identity.

## Falsifier

A natural index whose literal formal coefficient differs from the stated
finite sum would refute the assertion. A counterexample to the separate
supercongruence would not refute this identity. Pointwise evaluation or
analytic division is not the coefficient operation quantified here.

## Evidence

The Lean declaration
`D5/S1/Recurrence/BalaTrinomialCoefficientIdentity.result` states the full
identity for every natural index. Its `source` definition forms the formal
quotient independently of the finite sum. The proof uses the existing
frozen `mobius` and `mobius_zero` declarations from
`D5/S1/Recurrence/Invariants/CompositionalIterateCongruence` and the original
`prefactor_subst_coeff` theorem from
`D5/S1/Recurrence/Invariants/MatharA000159Recurrence`. The latter is applied
over the rationals with prefactor $(1-X)^{n-1}$ and $W=(1-X)^{-1}$;
the existing Möbius definition identifies its inner series $XW$.
Pinned Mathlib coefficient, inverse, binomial and polynomial-degree
results supply the remaining coefficient transport and finite sum.
The corresponding Blueprint attaches a typed `Proved` resolution to this
single result.

## Triage

Tier 1 external named OEIS conjecture. The admission basis is
`open-problem-resolution`, with
[the original exact-event preregistration](https://github.com/the-omega-institute/trureturing/issues/26252#issuecomment-6617121132).
The result has proof shape `bind-only`: after inlining its auxiliary
declarations, it applies the frozen prefactor substitution formula,
coefficient and polynomial-degree bounds, and binomial and inverse-series
formulas, with finite-sum, index and ring normalization. The auxiliary
declarations are consumed on the result's proof path; no new content
witness is asserted. Utility is `none`. The resolution concerns the finite identity
alone and asserts no supercongruence or new general algorithm.

## ASSUMED-UNVERIFIED

Worldwide openness, priority, exhaustive literature coverage and the
correctness or equivalence of the jOEIS and LODA implementations remain
unverified beyond the bounded readings in the source note. No independent
resolution of the neighboring supercongruence follows. The typed audit's
unknown continuation records an unknown residual; it asserts neither
undecidability nor inexhaustibility.
