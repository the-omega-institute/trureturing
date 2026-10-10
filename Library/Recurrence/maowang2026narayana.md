---
bibkey: maowang2026narayana
authors: Jianxi Mao and Lijie Wang
year: 2026
title: The Narayana transformation
doi: null
url: https://arxiv.org/abs/2607.01572v1
claim: Conjecture 4.1 asks for real nonpositive roots of the row polynomials of the ordinary squares of the Eulerian and Delannoy triangles.
strata_touched:
  - D5/S1/Recurrence/Algebraic/DelannoySquareRoots
license: citation-only
triage: anchor
---

# The original Delannoy matrix-square question

Jianxi Mao and Lijie Wang, *The Narayana transformation*,
arXiv:2607.01572v1, Concluding remarks and open problems, PDF page 11.
The source TeX has SHA-256
`933bc8b944c095032f70fc562ebd3e7beee68423797b495f28a3fe375e3df871`.

The source defines `D(n,k)` as the number of lattice paths from `(0,0)`
to `(n-k,k)` using steps `(1,0)`, `(0,1)` and `(1,1)`. The triangle
has row zero `[1]` and is zero outside `0 <= k <= n`. Its square is
ordinary matrix multiplication:

\[
G(n,k)=\sum_{j=k}^{n}D(n,j)D(j,k),\qquad
G_n(x)=\sum_{k=0}^{n}G(n,k)x^k.
\]

The source derives

\[
\sum_{n\ge0}G_n(x)t^n=
\frac{1-t}{(1-t)(1-2t-t^2)-xt(1+t)(1+t^2)}.
\]

Conjecture 4.1 states:

> The RGFs of A² and D² have only real nonpositive roots.

The selected question is the `D²` clause. The Eulerian clause, higher
powers, simplicity and interlacing are outside its scope. The strict
negative-root version is equivalent for this triangle because the constant
coefficient of each squared row is positive.

The formal source counts actual ordered step words and derives the displayed
generating function from their endpoint enumeration and the finite matrix
product. Its endpoint exclusion says that the ordinary Delannoy row
polynomial is nonzero at `1-sqrt(2)` in every degree. This excludes a
boundary zero in the proposed complementary root-count argument; it does
not prove the conjecture by itself.

For complex `u,v,y` satisfying `u != 0`, `v != 0`, `u+v+uv=1` and
`yuv=1`, the formal bridge also proves, for every natural `n`,

\[
y(v-u)(-1)^nG_n(-y)=
\frac{T_n(-u)}{u^{n+1}}-\frac{T_n(-v)}{v^{n+1}}.
\]

The original squared-row series is used on the left. The identity is valid
in multiplied form even when `u=v`; its quotient use requires distinct
parameters. The complementary root counts remain unformalized.

The bounded source comparison distinguishes ordinary Delannoy rows from
the squared rows. Chebyshev-root formulas and generic continuity or
factorization theorems supply reusable ingredients, not a resolution of
this original matrix-square question. No exhaustive publication-absence or
priority claim is made.
