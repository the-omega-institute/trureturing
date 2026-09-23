---
slug: perrier-multidimensional-continued-fraction-generating-functions
bibkey: perrier2026mcf
doi: 10.54550/ECA2026V6S4R33
url: https://ecajournal.haifa.ac.il/Volume2026/ECA2026_S4R33.pdf
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions
---

# Perrier's period-one generating functions

## Problem

Rachel Perrier, *Multidimensional Continued Fractions and Riordan Arrays*,
Enumerative Combinatorics and Applications 6:4 (2026), Section 5, printed
pp. 14–15, gives the period-one recurrence with initial values
$r_1^{(-1)}=1$ and $r_{j+1}^{(-1)}=a_j$ for $1\le j\le k-1$:

$$
r_1^{(n+1)}=r_k^{(n)},\qquad
r_{j+1}^{(n+1)}=r_j^{(n)}+m_jr_k^{(n)}.
$$

The source states on printed p. 15:

> We conjecture that solving these recurrences yields

$$
R_1(t)=\frac{1+\sum_{j=1}^{k-1}(a_j-m_j)t^{k-j}}
{1-\sum_{j=1}^{k-1}m_jt^{k-j}-t^k},\qquad
R_k(t)=\frac{t^{k-1}+\sum_{j=1}^{k-1}a_jt^{k-1-j}}
{1-\sum_{j=1}^{k-1}m_jt^{k-j}-t^k}.
$$

The finite sums reproduce the two printed numerators and their common
denominator. The shifted convention is
$R_i(t)=\sum_{n\ge0}r_i^{(n-1)}t^n$, explicitly defined on printed pp. 8
and 12. Section 5 introduces higher dimensions with the sentence
‘The same method extends to higher dimensions.’ It does not repeat the
definition of the generating functions; retaining that shift is the
contextual reading used here.

Set $k=d+1$. Lean time $n$ represents source time $n-1$, coordinate
$j:\operatorname{Fin}(d+1)$ represents source coordinate $j+1$, and
$m,a:\operatorname{Fin}(d)\to K$ likewise use zero-based indices.
For every commutative ring $K$, every natural $d$, every parameter pair,
and every sequence satisfying the initial values and both recurrence
equations, the formal result is:

```lean
theorem result {K : Type*} [CommRing K] {d : ℕ}
    (m a : Fin d → K) (r : ℕ → Fin (d + 1) → K)
    (h : Recurrence m a r) :
    R r 0 * D m = P m a ∧ R r (Fin.last d) * D m = Q a
```

Here `R` is the power series with coefficients `r`; `D`, `P`, and `Q`
are exactly the denominator and two numerators above, with constants
embedded in $K[[X]]$. All finite sums are empty when $d=0$; the result
includes this case. The initial vector and next-vector rule recursively
determine a unique sequence for every parameter pair.

## Motivation

This settles the two conjectured generating-function formulas for every
dimension in the period-one case. The arbitrary commutative-ring domain
includes the paper's integral setting. The denominator has constant
coefficient one and hence is a unit in the formal power-series ring;
the multiplicative identities therefore express the printed quotients
without requiring a field or division syntax.

## Gap

The article proves the two- and three-dimensional cases and states the
general formulas as a conjecture in Section 5. The target and the
commutative-ring domain correction are recorded in
[preregistration #8627](https://github.com/the-omega-institute/trureturing/issues/8627).
This is a tier-one external conjecture, admitted under
`admission_basis: open-problem-resolution`.

The proof shape of the sole theorem `result` is `bind-only`: coefficient
identities, finite-sum reindexing, and ring normalization from pinned
Mathlib discharge the statement. There is no escape witness and no
separate helper theorem declaration. Its direct import is
`Mathlib.RingTheory.PowerSeries.Inverse`; it imports no D5 module.
The five definitions supply the recurrence and its series notation.
Utility is `none`: the delivery is a symbolic identity with unbounded
dimension, not a finite enumeration, certified instance, checker, or
numerical reduction.

## Route

1. Translate the coefficient recurrence into power-series equations,
   including $R_1=1+XR_k$.
2. Multiply the successor-coordinate equations by $X^{k-1-j}$ and sum.
   The two decompositions of the same finite sum cancel the intermediate
   coordinates, leaving an equation for $R_k$.
3. Substitute the first-coordinate equation and collect terms to obtain
   $R_kD=Q$.
4. Normalize $D+XQ=P$ and multiply $R_1=1+XR_k$ by $D$ to obtain
   $R_1D=P$.

## Falsifier

A commutative ring, dimension, parameter pair, and recurrence solution
for which a coefficient of either product identity differs from its
numerator would refute the formal statement. Comparing an unshifted
generating function instead would test a different statement.

## Evidence

The complete proof is `result` in
`D5/S1/Recurrence/Algebraic/PerrierPeriodicGeneratingFunctions.lean`.
Its public surface consists of `Recurrence`, `R`, `D`, `P`, `Q`, and
`result`. The corresponding Scribe theorem node binds this dossier to
that result with `OpenProblemResolutionClaim` and `ResolutionKind.Proved`.
The source quotations, printed-page locators, coefficient-domain
discussion, and expanded formulas are retained in
`Library/Recurrence/perrier2026mcf.md`.

## Triage

`theorem`; resolution `proved` for the two period-one shifted generating
functions in Section 5. The subsequent conjecture concerning the
generalized recurrence in equation (7) is outside this result, as are
periods greater than one and analytic convergence of the series.

## ASSUMED-UNVERIFIED

The author's 2023 Washington State University thesis, reference [22] in
the article, was not retrieved in the inherited source assessment.
Whether it already proves the general case remains unverified. The
article's explicit conjecture is the source of the target; historical
openness beyond the documented source assessment and exhaustive novelty
or priority are not established.
