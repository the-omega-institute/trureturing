---
slug: bardakov-2024-simplex-fixed-point-free-permutations
bibkey: bardakov2024simplex
doi: 10.1134/S1055134424010012
url: https://arxiv.org/abs/2206.08906v1
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result
---

# Fixed-point-free permutation solutions of the n-simplex equation

## Problem

V. Bardakov, B. Chuzinov, I. Emel'yanenkov, M. Ivanov, T. Kozlovskaya and
V. Leshkov, *Set-theoretical solutions of simplex equations*,
arXiv:2206.08906v1, Section 4.2 (Question 4.22 of Siberian Adv. Math.
34(1) (2024) 1–40, and of its Russian original in Мат. труды 27(1) (2024)),
ask:

> 2) We know that the permutation $P_{12}$ is a solution of the YBE. For which $n > 2$ there are non-identity permutations without fixed points that gives solutions of the \SE?

The $n$-simplex equation $R_{\overline 1}\cdots R_{\overline{n+1}} =
R_{\overline{n+1}}\cdots R_{\overline 1}$ acts on $X^N$, $N=n(n+1)/2$, with
the multi-indices given by the rows of the matrix $MI_n$; a permutation $s$
gives the simple map $(x_1,\dots,x_n)\mapsto(x_{s(1)},\dots,x_{s(n)})$.
The precise question, preregistered in issue #11874, asks for the set of
$n>2$ for which some permutation without fixed points gives a solution on
every set.

## Motivation

The $n$-simplex equations generalize the Yang–Baxter equation ($n=2$) and
Zamolodchikov's tetrahedron equation ($n=3$), the integrability conditions
of vertex models in higher dimension. The frozen declaration
`D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result`
answers the question: exactly the even $n$.

## Gap

Issue #11874 classifies the question as Tier 1 and records the bounded
literature check before any Lean: the arXiv text and the journal version keep
the question; Hietarinta's classification of permutation-type solutions
(J. Phys. A 30 (1997) 4757) covers $n\le4$ only; the eleven citing works
listed by Semantic Scholar and sixteen later simplex-equation sources do not
address fixed-point-free permutation solutions.

The existence half for even $n$ is nevertheless implied by published work.
In the paper itself, Proposition 4.13 of arXiv:2206.08906v1 (l. 992–996)
states that $R\times A$ solves the $(n+m)$-simplex equation whenever $R$ solves
the $n$-simplex equation and $A$ is one of the maps of Example 4.12, among
them $P(x,y)=(y,x)$; repeating it from $R=P$ gives the product of the
transpositions of adjacent pairs for every even $n$. Independently,
Theorem 6.7 of S. M. Mihalache and T. Mochida, *Constructing Solutions of
Simplex Equations from Polygon Equations*, arXiv:2510.12905v4, states that for
a solution $T$ of the $(2k+1)$-gon equation and a solution $S$ of its dual
satisfying their mixed relation,
$\sigma_{1,2}\sigma_{3,4}\cdots\sigma_{2k-1,2k}T_{2,4,\dots,2k}S_{1,3,\dots,2k-1}$
solves the $2k$-simplex equation on $V^{\otimes 2k}$, whose multi-indices are
the rows of $MI_{2k}$ (their matrix $A_{4k+1}$ obeys the recursion of $MI_{2k}$,
from $A_3=MI_1=[1,1]^{\mathsf T}$); the paper attributes the proof for the odd-gon
equations to A. Dimakis and I. G. Korepanov, J. Math. Phys. 62 (2021) 051701.
The identity maps satisfy the polygon equation, its dual and the mixed
relation, so the product of the transpositions of adjacent factors solves the
linear $2k$-simplex equation; restricted to the basis tensors of $V$ with basis
$X$, it is the simple map on $X^{2k}$ of the fixed-point-free involution of
the $2k$ coordinate positions.
Mihalache and Mochida cite the paper of Bardakov et al. only for general
properties of simplex equations; they do not state this specialization or
mention Question 2. The new content of
this settlement is the non-existence for odd $n$ and the classification of
simple solutions behind it; the existence for even $n$ is proved here directly.

These are orchestrator-reported literature readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty or exclude an independent answer.

## Route

1. Index the coordinates by the edges $\{a,b\}$, $0\le a<b\le n$, of the
   complete graph on the vertices of the simplex; row $v$ of $MI_n$ lists the
   edges at $v$ in increasing order of the other endpoint. For the simple map
   of $s$, the operator of $v$ composes a configuration with the map
   $\sigma_v$ sending the edge in slot $j$ at $v$ to the edge in slot $s(j)$.
   So the two sides are $x\circ(\sigma_n\cdots\sigma_0)$ and
   $x\circ(\sigma_0\cdots\sigma_n)$, and the simple map is a solution on
   every set exactly when the two edge maps agree.
2. Following the edge $\{i,i+1\}$ through the vertices in increasing and in
   decreasing order gives $\{s(i),s(i)+1\}$ or $\{s(i),i\}$, and
   $\{s(i),s(i)+1\}$ or $\{i+1,s(i)+1\}$; they agree only when
   $|s(i)-i|\le1$.
3. If $|s(j)-j|\le1$ for every $j$, each edge $\{a,b\}$ reaches the same edge
   in both orders: $\{a,a+2\}$ when $b=a+2$, $s(a)=a+1$, $s(a+1)=a$;
   $\{s(a),s(a)+1\}$ when $b=a+1$; and $\{s(a),s(b-1)+1\}$ otherwise.
4. A permutation without fixed points that moves every index by at most one
   has displacements $s(i)-i=\pm1$ summing to $0$, so
   $n=\sum_i(s(i)-i+1)$ is a sum of even numbers.
5. For even $n$, the involution exchanging $2t$ and $2t+1$ has no fixed point
   and moves every index by one, so by step 3 its simple map is a solution.

## Falsifier

An odd $n>2$ with a fixed-point-free permutation solution, or an even $n>2$
without one, would contradict the answer; the kernel-checked `result`
excludes both. Changing the order of the edges at a vertex, or the
hypothesis that the map solves the equation on every set, changes the
question.

## Evidence

Exhaustive computation from the paper's recurrence for $MI_n$ (issue #11874)
gives $1,2,3,5,8,13,21,34$ permutation solutions for $n=1,\dots,8$, with a
fixed-point-free one exactly for $n=2,4,6,8$, each time only
$(2,1,4,3,\dots)$; as controls, $(3,4,1,2)$ is not a solution for $n=4$, and
$Pr^3_2$ and $(x,x,y)$ are solutions for $n=3$ while $(z,y,x)$ is not.

The canonical source is
`D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.lean`.
Its public declarations are `Edge`, `slotEdge`, `opR`, `lhs`, `rhs`,
`IsSolution`, `simpleMap`, `claim` and `result`. The frozen module state has
statement identity `sha256:d0205cfa10961c9d2800201a9e139de9e748af708d43c5e3d8f86909faf0920f`. The result declaration has statement identity
`sha256:35f02a88813776f318ae998276e0e66a1b5a95939272122a739f564edab027cd`. The Freeze event is `sha256:9346aeb3ff3a0a4552e8628110c514079879bea6f0c69682963c7a3281102acd`. It has no project-level frozen
prerequisites (pinned Mathlib only). The proof uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom. The private theorem `chain_values` proves
steps 2 and 3 on pairs of natural numbers; `result` proves step 1 for every
map `s`, and steps 4 and 5.

## Triage

Tier 1 published question; resolution `Proved` by
`D5/S3/StatisticalMechanics/VertexModels/SimplexFixedPointFreePermutations.result`.
`proof_shape: content`; `admission_basis: open-problem-resolution`
(issue #11874). Utility `none`: the result is a theorem over every $n>2$.

### What the settlement shows

- **Proved in this module:** for every $n>2$, there is a permutation without
  fixed points whose simple map solves the $n$-simplex equation on every set
  iff $n$ is even; this answers Question 2.
- **Implied by published work, not new here:** the existence for even $n$,
  from Proposition 4.13 of the paper applied repeatedly to $P$, and also as
  the specialization of Theorem 6.7 of arXiv:2510.12905v4 to identity polygon
  solutions (see Gap).
- **Follows from the private `chain_values` and the edge-map facts inside
  `result`, not stated as a declaration:** for every map $s$ of
  $\{0,\dots,n-1\}$, the simple map of $s$ solves the equation on every set
  iff $|s(i)-i|\le1$ for all $i$. This classifies all simple solutions, not
  only permutations.
- **Follows, not stated as a declaration:** the fixed-point-free permutation
  solution for even $n$ is unique, the product of the transpositions of
  $2t$ and $2t+1$, since a permutation moving every index by one must pair
  $0$ with $1$, $2$ with $3$, and so on.
- **Computed, not formalized:** the permutation solutions number
  $1,2,3,5,8,13,21,34$ for $n\le8$ (orchestrator), and the simple solutions
  $1,4,12,36,108,324,972$ for $n\le7$ (scout reading), in issue #11874.
- **Open here:** Question 1 of the same paper, on indecomposable simple
  solutions other than the five listed maps, is not settled by this module;
  for $n=3$ the paper's own list of verbal solutions in abelian groups
  already contains such maps.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish worldwide priority or
absence of an independent solution; in particular the full text of the
English journal version was not read, and the Dimakis–Korepanov paper was
not read: its role for the odd-gon case is as stated by Mihalache and Mochida.
The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper,
including the identification of the coordinates with edges through the rows
of $MI_n$, is checked by reading the source, the definitions and the mirror,
and by the computation for $n\le8$.
