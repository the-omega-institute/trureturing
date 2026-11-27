---
slug: oeis-a005926-diamond-summatory-asymptotic
bibkey: kotesovec2026a005926
doi: null
url: https://oeis.org/A005926/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Lattices/Counting/ShiftedBallCount.shifted_limit
---

# Vaclav Kotesovec’s summatory conjecture for OEIS A005926

## Problem

OEIS A005926 revision 49 attributes the following conjecture to Vaclav Kotesovec on November 26, 2026. [OEIS A005926, FORMULA](https://oeis.org/A005926/internal)

> Conjecture: Sum_{k=1..n} a(k) ~ Pi*n^(3/2)/48.

Over the integers, let $T(j)=j(j+1)/2$ and $\psi(X)=\sum_{j\ge0}X^{T(j)}$.
The source defines $a(k)$ as the coefficient of $X^k$ in
$X^3(\psi(X^8)^3+\psi(-X^8)^3)$. The claimed asymptotic is through all
natural cutoffs $N$, with the sum from $1$ through $N$ inclusive.

## Motivation

The generating function relates the diamond theta coefficients to
integer triples in a shifted three-dimensional ball. Its two signed
cubes impose a parity condition, whose contribution to the leading
constant can be counted using the four even residue classes.

## Gap

The published coefficient formula identifies the sequence degree by
degree. The conjecture asks for a single limit over the cumulative
count with the native cutoff and with the leading constant $\pi/48$.
[Formalization scope, issue #34748](https://github.com/the-omega-institute/trureturing/issues/34748)

## Route

The two cubes give weight two to even total triangular degree and
weight zero to odd total triangular degree. For an integer coordinate
$z$, write $j=2z$ if $z\ge0$ and $j=-2z-1$ otherwise. This bijects the
integers with the naturals and gives $8T(j)+1=(4z+1)^2$ and
$T(j)\equiv z\pmod{2}$. Thus the inclusive sum is twice the number of
integer triples with even coordinate sum and $\sum_i(4z_i+1)^2\le N$.

The even residue patterns modulo two are $000$, $011$, $101$ and
$110$. In each class the coordinates $4z_i+1$ lie on a translate of the
integer grid of spacing eight. The corresponding ball has radius
$\sqrt{N}/8$ in unit grid coordinates. Its normalized count contributes
$(4\pi/3)/8^3$ per class, so four classes with weight two give $\pi/48$.

## Falsifier

A mismatch in the formal-series coefficients, either endpoint of the
inclusive sum, or the class count or its spacing would invalidate the
source correspondence. At $N=0$ the sum and the lattice region are both
empty. The limit uses natural $N\to\infty$ and includes all residue
classes of the cutoff.

## Evidence

`D5/S3/Analytic/Asymptotics/OeisA005926Diamond.result` proves convergence
of the exact normalized sum to $\pi/48$. It uses
`PowerSeries.coeff` on the native formal series and `Finset.Icc 1 N`
for the sum. The proof uses `Classical.choice`, `Quot.sound` and
`propext`.

## Triage

The resolution covers the full conjecture in A005926. For A217513, write
$S(N)=\sum_{k=1}^N a(k)$. The support in degrees $16m+3$ gives
$\operatorname{A217513}(m)=S(16m+3)$ and, for $N\ge3$,
$S(N)=\operatorname{A217513}(\lfloor(N-3)/16\rfloor)$. Since
$16\lfloor(N-3)/16\rfloor/N\to1$, the two asymptotics are equivalent.
[OEIS A217513, FORMULA](https://oeis.org/A217513/internal)

## ASSUMED-UNVERIFIED

Worldwide priority and completeness of the literature search are
unverified. The source and the lattice-point theorem used in the proof
are identified in the Library note.
