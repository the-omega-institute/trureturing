---
slug: blitvic-kammoun-steingrimsson-2026-packing-maximum
bibkey: blitvickammounsteingrimsson2026patterns
doi: 10.48550/arXiv.2610.29846
url: https://arxiv.org/abs/2610.29846v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result
---

# The whole prescribed packing-maximum conjecture

## Problem

Blitvić–Kammoun–Steingrímsson, *Permutations, Pattern Covers, Posets and
Positivity: Part I: Patterns and Posets*, arXiv:2610.29846v1, Section 7
item 4, Conjecture 7.1:

> For overlap $m\le K/2$, the maximum is obtained when prefix and suffix
> are interleaved and minimal, that is, for patterns with prefix
> $135\ldots(2m-1)$ and suffix $246\ldots(2m)$.

For every $K\ge2$, $1\le m<K$, $2m\le K$, $j\ge1$, the assertion
requires a prescribed pattern $\rho$ with
$C(\pi,m,j)\le C(\rho,m,j)$ for every compatible pattern $\pi$.
The middle order of $\rho$ is unrestricted. Here $C$ counts actual
permutations of length $K+(j-1)(K-m)$ having all prescribed windows;
extra occurrences are permitted. Compatibility means that prefix and
suffix have the same relative order. The formal comparison domain does
not impose a normalization or identify patterns by symmetry.

## Motivation

The source's packing/poset correspondence turns this into an extremal
linear-extension question. Minimal interleaved prefix/suffix produce a
grid-like poset, but changing the sizes of independent rank groups can
increase the count. A finite strict comparison decides the whole universal
maximum-attainment assertion without determining an actual maximum.

## Gap

The whole assertion is refuted by the exact finite comparison below.
The actual maximum and the strict-overlap range remain separate questions.

## Route

At $K=8,m=4,j=2$, use $\pi=13472568$ and $\rho=13572468$.
The middle is empty, and all prescribed patterns equal $\rho$.
Both patterns are compatible and satisfy the source's increasing and
first-value convention. The exact source count is transported through
an equivalence between actual finite permutations and injective rank
assignments with precisely the same window comparisons.

Writing $x_i$ for one-based entries, the competitor's two chains are

$$
x_1<x_5<x_2<x_3<x_6<x_7<x_4<x_8,\qquad
x_5<x_9<x_6<x_7<x_{10}<x_{11}<x_8<x_{12}.
$$

They force ordered groups
$x_1<x_5<\{x_2,x_3,x_9\}<x_6<x_7<\{x_4,x_{10},x_{11}\}<x_8<x_{12}$,
with $x_2<x_3$ and $x_{10}<x_{11}$. The groups have three choices each.
For the prescribed pattern, the groups are
$x_1<x_5<\{x_2,x_9\}<x_6<\{x_3,x_{10}\}<x_7<\{x_4,x_{11}\}<x_8<x_{12}$,
with two choices in each pair. The certificate proofs establish necessity
from the chains and injectivity, and sufficiency by checking every
original pairwise window comparison. Hence the counts are $3^2=9$ and
$2^3=8$, with no multiplicity or omitted source permutation.

## Falsifier

The whole source assertion implies $9\le8$ at this admitted triple.
A missing source packing, an invalid listed function, a mismatch in the
source predicate, or an additional prescribed boundary pattern would
invalidate the finite argument. The Lean membership equivalences and
boundary theorem address precisely these possibilities.

## Evidence

The module `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.lean`
defines the closed `claim : Prop` and proves the literal `result : ¬ claim`.
`windowIndex` carries a proof that every prescribed index is in the exact
permutation length. `encodingEquiv` has both inverse laws;
`source_cardinality` transports cardinality. `count_competitor` and
`count_prescribed` prove both exact original counts, and
`prescribed_boundary` covers the full prescribed family at $K=8,m=4$.

The new finite lists contain nine and eight actual rank assignments.
Their completeness proofs use the exact source chains and injectivity;
their soundness proofs check all original comparisons. There is no
`sorry`, new axiom, assumed recurrence or asymptotic approximation.
The module is a canonical frozen member, with a typed Refuted resolution
on its result in the corresponding Blueprint Scribe. Its claim and result
retain the exact whole-source assertion and its literal negation.

The preregistered external problem is
https://github.com/the-omega-institute/trureturing/issues/20263 .
The admission basis is the whole named open-problem resolution; ordinary
finite arithmetic and representation ingredients receive no separate
novelty claim.

## Triage

1. **Proved in Lean:** the whole maximum-attainment
   assertion is false, with exact counts $9>8$ at the displayed triple.
2. **Proved in Lean:** the source permutation and
   rank-assignment cardinalities agree, and every prescribed boundary
   pattern equals $13572468$.
3. **Mechanism:** two independent three-way choices beat three independent
   binary choices. This explains the finite failure; it is not a theorem
   classifying extremizers at other parameters.
4. **Open:** the actual maximum and all maximizing patterns at this or
   other triples; the strict-overlap range $2m<K$; repaired sufficient
   conditions; the separate cutoff question in Section 7 item 8.
5. **Delivery boundary:** final independent implementation reviews,
   required CI and dev integration are distinct from the mathematical
   refutation and its frozen membership.

## ASSUMED-UNVERIFIED

No exhaustive literature absence or worldwide priority is claimed.
The bounded literature scope and attribution are given in the owning
Library note. Historical ordinary computation and independent ordinary
audit are supporting source evidence, not substitutes for the current
Lean proof or final delivery checks. Provider memory is UNKNOWN.
