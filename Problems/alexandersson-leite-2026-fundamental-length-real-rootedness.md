---
slug: alexandersson-leite-2026-fundamental-length-real-rootedness
bibkey: alexanderssonleite2026sinkpolynomials
doi: 10.48550/arXiv.2610.41502
url: https://arxiv.org/html/2610.41502v1#S6.Thmtheorem7
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result
---

# Alexandersson–Leite Question 6.7, weighted fundamental-length real-rootedness

## Problem

> In particular, is $\Psi_t(X_{H_h}(X;q))$ real-rooted for every such $h$ and $q$?

For every positive integer $n$, the function $h\colon[n]\to[n]$ is weakly
increasing and satisfies $i\le h(i)$. Edges of $H_h$ are the pairs
$i<j\le h(i)$. The real weight satisfies $q\ge0$. A proper coloring
$\kappa\colon[n]\to\mathbb Z_{>0}$ contributes the monomial
$\prod_i x_{\kappa(i)}$ with weight $q^{\operatorname{asc}(\kappa)}$, where
an ascent is an edge with $i<j$ and $\kappa(i)<\kappa(j)$. The linear map
$\Psi_t$ sends $F_{n,S}$ to $t^{|S|+1}$ and sends $1$ to $1$.
[Question 6.7](https://arxiv.org/html/2610.41502v1#S6.Thmtheorem7) ·
[§5.2](https://arxiv.org/html/2610.41502v1#S5.SS2) ·
[§5.3](https://arxiv.org/html/2610.41502v1#S5.SS3) ·
[§6.1](https://arxiv.org/html/2610.41502v1#S6.SS1)

## Motivation

Corollary 6.2 establishes real-rootedness for the ordinary chordal chromatic
case. The final clause asks whether the fundamental-length map has the
same property for every nonnegative ascent weight on natural unit interval
graphs. The weighted elementary-length specialization already has an
all-weight theorem for this graph family.
[Corollary 6.2](https://arxiv.org/html/2610.41502v1#S6.Thmtheorem2) ·
[Theorem 5.2](https://arxiv.org/html/2610.41502v1#S5.Thmtheorem2)

## Gap

The fundamental and elementary maps use different coordinates. The path
test requires identifying the exact fundamental image of the
positive-integer coloring sum and then checking its roots.
[Fundamental length](https://arxiv.org/html/2610.41502v1#S6.SS1) ·
[Elementary sink specialization](https://arxiv.org/html/2610.41502v1#S5.SS3)

## Route

Choose $h=(2,3,4,4)$ and $q=16$. The edges are the three consecutive
pairs. Record a monomial by the strict positions $T$ in its sorted color
word. Increasing relabeling to the ranks of its colors preserves each
multiplicity, properness, and ascents. For any $S$, the basis element
$F_{n,S}$ contains precisely the monomial coordinates with $S\subseteq T$.
The monomial weight $t^{|T|+1}(1-t)^{n-|T|-1}$ sums over these supersets
to $t^{|S|+1}$. Möbius inversion on the lattice of cut sets gives uniqueness.

Grouping the coloring sum by the number $r$ of colors turns each weight
into $t^r(1-t)^{4-r}$ times the ascent-weighted sum over proper surjections
to $[r]$. The weights for $r=2,3,4$ are $272,2448,7089$.
The resulting polynomial is $t^2(272+1904t+4913t^2)$ and the residual
quadratic has discriminant $-1720128$.

## Falsifier

The argument requires the four-vertex witness to satisfy every source
hypothesis, the finite palettes to preserve the coefficients and the
fundamental prescription, and the residual quadratic to have strictly
negative discriminant.

## Evidence

The closed proposition and its literal negation are formalized as
`D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.claim` and `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result`. The Lean proof uses native Mathlib graph
colorings, real polynomials and polynomial splitting. The histogram is
checked by kernel reduction. The proof transfers the splitting
assumption through the two linear factors at zero and excludes a real
root of the remaining quadratic.
[Lean result](../D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.lean) ·
[Pinned citation](../Library/Certificates/alexanderssonleite2026sinkpolynomials.md) ·
[Problem #33678](https://github.com/the-omega-institute/trureturing/issues/33678)

## Triage

### What the settlement shows

The weighted fundamental-length assertion fails on a path with four
vertices. The two factors at zero account for two real roots, and the
strictly negative discriminant excludes real roots of the remaining
quadratic. This is proved by `D5/S3/Combinatorics/Graph/PrincipalSpecialization/AlexanderssonLeiteFundamentalLengthRefutation.result`.

The source's ordinary $q=1$ result for chordal graphs remains applicable
to this path. The all-$q\ge0$ elementary-length theorem remains applicable
to natural unit interval graphs. The source's reciprocity identity also
transfers the nonreal roots of this example to the corresponding
$\omega$-image at the source level. The wider classification of normalized
maps in Question 6.7 remains open here.
[Corollary 6.2](https://arxiv.org/html/2610.41502v1#S6.Thmtheorem2) ·
[Theorem 5.2](https://arxiv.org/html/2610.41502v1#S5.Thmtheorem2) ·
[§6.4](https://arxiv.org/html/2610.41502v1#S6.SS4)

## ASSUMED-UNVERIFIED

The bounded literature check found no earlier resolution of the weighted
clause. Worldwide priority and completeness of citation coverage are
unverified. The reciprocity consequence uses the source's identity
outside the Lean claim. The refutation does not establish minimality.
