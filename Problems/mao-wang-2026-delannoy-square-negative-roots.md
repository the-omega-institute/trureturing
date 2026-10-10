---
slug: mao-wang-2026-delannoy-square-negative-roots
bibkey: maowang2026narayana
doi: null
url: https://arxiv.org/abs/2607.01572v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/DelannoySquareRoots.source_correspondence
  - D5/S1/Recurrence/Algebraic/DelannoySquareRoots.upper_circle_roots
---

# Negative roots of the original Delannoy matrix square

## Problem

Conjecture 4.1 of Mao and Wang, *The Narayana transformation*, asks whether
the row polynomials of `A²` and `D²` have only real nonpositive roots.
The target here is only the original path-count `D²` clause.

For every natural `n` and complex `z`, the exact target is

\[
G_n(z)=0\quad\Longrightarrow\quad \operatorname{Im}z=0
\quad\hbox{and}\quad\operatorname{Re}z<0.
\]

Here `D(n,k)` counts actual E/N/NE paths to `(n-k,k)` and
`G(n,k)=sum_(j=k)^n D(n,j)D(j,k)`. Row zero is the constant polynomial one.
The target has no assumptions about root counts, interlacing, recurrence
stability or real-rootedness of a surrogate family.

## Motivation

The actual path-count square is a recent source question distinct from
ordinary Delannoy root formulas and from the Eulerian clause.

## Gap

The available formal prerequisite is `source_correspondence`: exact path
enumeration, the original matrix-square generating function in every degree,
nonvanishing of the ordinary row at `1-sqrt(2)`, and the universal quadratic
divided difference. The theorem `upper_circle_roots` constructs at least N
distinct actual squared-row roots in the central interval in every degree,
where N counts ordinary-row zeros above `sqrt(2)-1`. The complex-root implication
remains open in Lean.

## Route

The remaining proof uses `P_n(y)=(-1)^n G_n(-y)` and the involution
`v=(1-u)/(1+u)`, with `y=1/(uv)`. The formal divided difference uses
`u != 0`, `v != 0`, `u+v+uv=1` and `yuv=1` and states

\[
y(v-u)P_n(y)=\frac{T_n(-u)}{u^{n+1}}-
\frac{T_n(-v)}{v^{n+1}}.
\]

It is proved for every degree from the original squared rows. Applying it as
a quotient additionally requires `v != u`.
The standard Chebyshev-U description supplies the ordinary-row zeros.
The threshold `a=sqrt(2)-1` is excluded by the formal endpoint result.

The root construction has two complementary parts. On
`u=-1+sqrt(2) exp(i phi)`, `0<phi<pi`, the formal argument crossing count
in `upper_circle_roots` produces `n-k` distinct actual positive roots of
`P_n`, where `k` counts
ordinary-row zeros below `a`. Alternating real Chebyshev samples must
produce `k-1` further roots when `k>=1`, in a disjoint interval.
Closed-arc argument continuity, endpoint phases, interior crossings,
polar realness, actual-root correspondence, strict parameter injectivity and
the central interval bounds are proved. The real-interval sample signs and
their distinct roots remain obligations. Dividing out these roots leaves
degree at most one;
realness of the remaining factor and positivity of the original coefficients
then recover the exact complex-root conclusion. When `k=0`, the circle
count alone must supply all `n` roots.

## Falsifier

Any natural row with a complex zero outside the strictly negative real axis
would refute the target. Failure of an auxiliary count would refute that
route without settling the original question.

## Evidence

The formal definition `negativeRoots` is the exact original complex-root
target. The theorem `source_correspondence` supplies the path, series,
threshold and divided-difference prerequisites. It does not prove
`negativeRoots`. The theorem `upper_circle_roots` proves the unconditional
central-interval root count with its actual ordinary-row factors. It neither
assumes the missing complementary count nor resolves the final target.

## Triage

`theorem`: the target is a universal mathematical assertion. There is no
formal resolution claim for Conjecture 4.1 or its `D²` clause.

## ASSUMED-UNVERIFIED

Literature absence and publication priority are not established. The bounded
comparison found no exact all-degree squared-row supplier; ordinary Delannoy
formulas and generic Chebyshev, argument-continuity, IVT and polynomial
division results do not by themselves discharge the complementary counts.
