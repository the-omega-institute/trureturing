---
slug: miro-roig-tran-strict-sign
bibkey: miroroigtran2020weak
doi: 10.1016/j.jalgebra.2019.12.029
url: https://arxiv.org/abs/2001.06143v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MiroRoigTranStrictSign.result
---

# The Miró-Roig--Tran Strict-Sign Conjecture

## Problem

Miró-Roig and Tran, immediately after the proof of Proposition 3.12 in
arXiv `2001.06143v1`, conjecture that for every integer `n>=2`,

```text
sum_{k=0}^n (-1)^k binom(2n+2,k)
  * (2n^2 - 1 - (2n-1)k)^(2n-1) < 0.
```

The sum, affine subtraction, and power in the formal owner are literal integer
operations. Proposition 3.12(c) has a separate `n>=4` premise for a preceding
weak-Lefschetz implication; the conjectural display following the proof
explicitly returns to every `n>=2`. The paper's finite computation through
`n=400`, empirical monotonicity suggestion, and WLP consequence are not the
formal target.

## Motivation

The exact external assertion was preregistered in
https://github.com/the-omega-institute/trureturing/issues/9765 before the proof
probe. The registration fixes the source, quantifiers, and strict inequality;
it does not establish worldwide novelty or priority.

The canonical endpoint is
`D5/S3/Combinatorics/MiroRoigTranStrictSign.result`. Its definition
`coefficient` is the displayed integer sum and its theorem covers every natural
`n>=2` without a bounded range or a proxy statement.

## Gap

The primary v1 article was read at Proposition 3.12 and the conjecture
immediately following it. A refreshed bounded later-source inspection covered:

- Boij and Lundqvist, arXiv `2010.01107v2`, especially Section 4;
- Booth, Singh and Vraciu, arXiv `2410.22542v3`;
- Boij and Lundqvist, arXiv `2608.22823v1`, including Lemma 3.3,
  Theorem 3.4 and Remark 3.5.

These sources treat broader almost-complete-intersection classifications,
fixed-degree weak Lefschetz questions, square and cube thresholds,
Hilbert-series estimates, Cremona transformations, and WLP counterexamples.
No proof of the exact strict coefficient inequality for all `n>=2` was found
in this inspected scope. Citation indices and all possible later publications
were not exhaustively inspected, so this is a bounded negative finding only.

The pinned Mathlib supplies the interval-calculus infrastructure and the
Pascal summation theorem used in the formal proof, but the inspected library
did not contain the complete strict-sign theorem. One knot-safe derivative of
a positive-part power is a minimal attributed port from Physlib commit
`50ac243729e00925f91224e3916cce74bb971edf`, file
`PhyslibAlpha/ClassicalMechanics/NortonDome/PosPartPow.lean`, by Zhi Kai Pong,
under Apache 2.0. The applicable license is retained at
`docs/reports/inoutbalance/physlib-LICENSE.txt`. The local port is to be retired
when an equivalent declaration becomes available in the repository's pinned
Mathlib.

## Route

For natural `m,q` and real `x`, define the single normalized finite
positive-part family

```text
T(m,q,x) = (1/q!) * sum_{k=0}^m
  (-1)^k binom(m,k) max(x-k,0)^q.
```

There is no parallel recursive spline representation. Set

```text
D_m(x) = T(m,m-2,x),
C_m(x) = T(m,m-3,x),
s_m = m/2 - 2/3,
Q_m(u) = D_m(s_m-u) - D_m(s_m+u).
```

Knot-safe differentiation gives `d T(m,q+1)/dx = T(m,q)` for `q>=1` at
every real point, including the knots. Direct applications of the pinned
Pascal summation theorem give the exact unit-window and centered recurrences

```text
D_(m+1)(x) = integral_[x-1,x] D_m(t) dt,
Q_(m+1)(u) = integral_[u-1/2,u+1/2] Q_m(t) dt.
```

The strict-curvature proof maintains a private simultaneous invariant from
order four: support of `D_m` in `[0,m]`, reflection
`D_m(m-x)=-D_m(x)`, global `Q_m(u)>=0` for every `u>=0`,
`Q_m(1/2)>0`, and strict decrease of `D_m` on the closed core
`[s_m,m-s_m]`. At the base, `Q_4(1/2)=1/18`. When a centered recurrence
window crosses zero, odd cancellation removes its symmetric portion and the
remaining interval lies where the global Q inequality applies. Continuity and
the positive half-offset value propagate strict positivity.

For the next curvature value, the left half of the core is divided into the
three branches `t=1/2`, `1/2<t<1`, and `1<=t<=7/6`; the half-offset Q
inequality and strict decrease of D settle those branches. Reflection supplies
the right half. The base curvature `C_4` is zero at both closed-core endpoints
`4/3` and `8/3`, so the public closed-core strict theorem correctly starts at
`m>=5` rather than making a false order-four endpoint claim.

For the coefficient theorem, take

```text
m = 2n+2,
x = (2n^2-1)/(2n-1).
```

The summands beyond `k=n` have zero positive part. Factoring the positive
denominator from the surviving terms yields the exact identity

```text
real(coefficient(n))
  = (2n-1)^(2n-1) * (2n-1)! * C_(2n+2)(x).
```

For `n>=2`, the order satisfies `m>=6` and `x` lies in the closed core.
Strict curvature makes the last factor negative and the other two factors are
positive. The boundary value `n=2` maps to `m=6`, `x=7/3`, the left endpoint
of the closed core; the integer coefficient there is `-26`. Thus the endpoint
case is covered by the same theorem rather than by a stronger hypothesis or a
separate finite check.

## Falsifier

Any natural `n>=2` for which the displayed literal integer sum is nonnegative
would refute the result. A candidate that changes the upper limit, performs the
affine subtraction in naturals, drops the strict sign, assumes only `n>=4`, or
proves a WLP or monotonicity statement addresses a different claim.

Within the proof route, a failure of global `Q_m(u)>=0` at any nonnegative
offset, a zero value of `Q_m(1/2)`, or failure of strict closed-core curvature
at an order at least five would break the induction used by the endpoint. The
known zeros of `C_4` at `4/3` and `8/3` are expected boundary data and explain
the theorem's `m>=5` hypothesis; they do not falsify the final target, which
uses `m>=6`.

## Evidence

The three formal owners expose exactly eleven public declarations:

```text
CardinalSplineRecurrence.T
CardinalSplineRecurrence.D
CardinalSplineRecurrence.C
CardinalSplineRecurrence.s
CardinalSplineRecurrence.Q
CardinalSplineRecurrence.T_hasDerivAt
CardinalSplineRecurrence.D_succ_eq_integral
CardinalSplineRecurrence.Q_succ_eq_integral
CardinalSplineStrictCurvature.cardinalSpline_strict_curvature
MiroRoigTranStrictSign.coefficient
MiroRoigTranStrictSign.result
```

The support, reflection, global-Q, half-offset, and strict-D assertions are
private induction invariants rather than additional public API. The spline
recurrences and strict-curvature theorem are live auxiliary results; the sole
published-resolution owner is `MiroRoigTranStrictSign.result`.

The source article is Rosa M. Miró-Roig and Quang Hoa Tran, *On the weak
Lefschetz property for almost complete intersections generated by uniform
powers of general linear forms*, *Journal of Algebra* **551** (2020), 209-231,
DOI `10.1016/j.jalgebra.2019.12.029`, arXiv `2001.06143v1`.

## Triage

First tier: a named published conjecture, preregistered in issue #9765.
`admission_basis: escape-witness`; `question_answered: the exact displayed
strict integer coefficient inequality for every n>=2`.

| Declaration | proof_shape | computational_content.kind | admission_basis |
| --- | --- | --- | --- |
| `coefficient` | N/A (definition) | none | escape-witness |
| `result` | content | none | escape-witness |

The live escape witness is the same-batch global cardinal-spline curvature
theorem together with the positive normalization from the literal integer sum
to the curvature value. The curvature proof propagates facts not supplied by
an existing frozen theorem or direct normalization: global reflected-difference
nonnegativity, strict half-offset positivity, and strict closed-core curvature.
The result is universally quantified and is not bounded enumeration, a
checker, numeric reduction, or a certified finite instance; `utility: none`.

## ASSUMED-UNVERIFIED

The later-proof search was bounded to the named primary and later sources plus
the recorded library checks. It does not establish worldwide absence,
publication priority, exhaustive citation coverage, or that no independent
proof exists. The broader weak Lefschetz statements and the empirical
monotonicity pattern in the original paper are not formalized or claimed here.
