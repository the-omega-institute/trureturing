---
slug: shlyk-convexity-index-eventual-existence
bibkey: shlyk2026partitionconvexity
doi: null
url: https://arxiv.org/html/2611.24835v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index
---

# Shlyk's eventual existence of every partition convexity index

## Problem

Shlyk states in §1.2 that “for any ξ ≥ 2, a sufficiently large n has
partitions of index ξ” and restates eventual existence in §3.1. The
first sentence of his earlier Conjecture 1 reads “For every ξ,
$C_ξ(n) \ne \varnothing$ for sufficiently large $n > n_0(ξ)$.”
The second sentence asks about the sizes of the classes at fixed
$n$. Section 3.1 also states that question separately.
[2026 §1.2](https://arxiv.org/html/2611.24835v1#S1.SS2.p1.1) ·
[2026 §3.1](https://arxiv.org/html/2611.24835v1#S3.SS1.p2.1) ·
[2018 §2, Conjecture 1](https://arxiv.org/pdf/1805.07989v2#page=4)

The eventual-existence assertion is that for every natural $k\ge 2$
there is a natural $N$ such that for every natural $n>N$ a partition of
$n$ has convexity index exactly $k$. A partition has natural
multiplicities $x_s$ for $1\le s\le n$ with $\sum_s s x_s=n$.
For a representation of size $r$, the summands are pairwise distinct
partitions $y^j$ of $n$, each different from $x$, and there are positive
real coefficients $\lambda_j$ with $\sum_j\lambda_j=1$ and
$x_s=\sum_j\lambda_j y^j_s$ for every $s$. Exact index $k$ requires
attainment by $k$ terms and $k\le r$ for every such representation.
A repeated summand can be consolidated by adding its coefficients.
[#32924](https://github.com/the-omega-institute/trureturing/issues/32924)

## Motivation

The convexity index measures the fewest other partitions required
to express a given nonvertex partition. Eventual existence forces
arbitrarily many index classes to coexist: for a finite list of
indices, take the maximum of their finitely many thresholds.

## Gap

The 2018 preprint gives small-index results through four. The 2026
paper reports 38 index-five examples at particular totals and studies
the vertex count. The bounded literature screen found no general
settlement in the consulted arXiv editions, indexed related work,
or Lean libraries. The publisher's journal full text and complete
citation coverage remain unverified. [Source and screen](https://github.com/the-omega-institute/trureturing/issues/32924)

Bradley's and Rosenberg's results supply prior work on strong integer
constraint aggregation. The partition application uses a particular
congruence fiber, verifies distinct positive part sizes, derives
summand support, and extends the exact index to every total above a
single threshold. [Bradley](https://doi.org/10.1016/0012-365X(71)90005-7) ·
[Rosenberg](https://doi.org/10.1016/0012-365X(74)90126-5) ·
[Poirion, Ky and Liberti](https://arxiv.org/pdf/1605.08742v4#page=2)

## Route

The a-coordinates sum to $k$ and have a common residue modulo $k$.
A nonzero residue forces the all-ones vector. With residue zero,
one coordinate equals $k$ and all others vanish. The remaining
coordinates are determined by pair and congruence equations.
Distinct matrix columns yield distinct positive encoded sizes.
The leading digit first bounds the total multiplicity of an arbitrary
supported partition. That bound puts all row sums below the radix and
allows exact recovery of the equations by uniqueness of digits.

Positivity forces each summand to stay on the center's support. Each
a-coordinate forces its own alternative, which gives a lower bound of
$k$ for arbitrary positive real weights. The equal-weight representation
attains it. For base total $m$ and $n>2m$, adjoining the part $n-m$ gives
that part multiplicity one in the center. Every summand has at most one
copy, and normalization forces every summand to have one. Deletion
preserves coefficients, cardinality, and distinctness.

## Falsifier

A falsifier would give some index $k\ge2$ and arbitrarily large totals
$n$ with $C_k(n)=\varnothing$, where $C_k(n)$ is the class of partitions
of $n$ whose minimum representation size is exactly $k$. A failure at
a particular small total is compatible with the threshold quantifier.

## Evidence

The theorem is
`D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index`.
Its typed Scribe statement displays the entire partition and
representation telescope. The recorded probe includes the full
quantified result and the earlier supported-fiber checkpoint.
[Preregistered outcome](https://github.com/the-omega-institute/trureturing/issues/32924#issuecomment-7068440383)

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| Every $k\ge2$ occurs at every $n$ above a strict threshold depending on $k$ | Proved | `D5/S3/Combinatorics/Partitions/ShlykConvexityIndex.shlyk_eventual_convexity_index` |
| Every finite family of indices at least two coexists at all sufficiently large totals | Proved | Take the finite maximum of the thresholds supplied by the theorem above, using zero for the empty family |
| Class-size monotonicity at fixed $n$ | Open | Separate statement in §3.1 and the second sentence of 2018 Conjecture 1 |
| Least total attaining a general index | Open | Separate question in 2026 §4 |

### What the settlement shows

The supported integer fiber forces all $k$ alternatives into any
positive representation of the center. The strict padding inequality
gives one threshold $2m$ that works over all larger totals. Consequently
the number of nonempty convexity-index classes is unbounded as the
total grows. Smaller thresholds and a sharp least total are outside the
proved statement.

## ASSUMED-UNVERIFIED

Global priority, completeness of the citation screen, and agreement of
the inaccessible publisher text with the checked preprint remain
unverified. The result settles the author-posed eventual-existence
assertion at the scope shown in the theorem.
