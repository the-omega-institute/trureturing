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
listed by Semantic Scholar, sixteen later simplex-equation sources and
Dimakis–Müller-Hoissen arXiv:2510.12905 do not address fixed-point-free
permutation solutions.

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
(issue #11874). Utility `none`: the result is a theorem over every $n$.

### What the settlement shows

- **Proved in this module:** for every $n$, the simple map of a permutation
  without fixed points solves the $n$-simplex equation on every set iff $n$
  is even; for $n>2$ this answers Question 2.
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
English journal version was not read. The Lean kernel verifies the encoded
statement and its axiom closure; correspondence to the external paper,
including the identification of the coordinates with edges through the rows
of $MI_n$, is checked by reading the source, the definitions and the mirror,
and by the computation for $n\le8$.
