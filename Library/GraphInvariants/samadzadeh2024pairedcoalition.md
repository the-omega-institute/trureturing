---
bibkey: samadzadeh2024pairedcoalition
authors: Mohammad Reza Samadzadeh; Doost Ali Mojdeh; Reza Nadimi
year: 2024
title: Paired coalition in graphs
doi: 10.1080/09728600.2024.2389070
url: https://arxiv.org/abs/2402.10842v4
claim: Conjecture 1 assigns paired coalition number 5 at height 2, 3 at odd heights, and 0 otherwise for perfect binary trees.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/SamadzadehMojdehNadimiRefutation
license: citation-only
triage: anchor
---

# Paired coalition in graphs

## Verified locator

DOI: 10.1080/09728600.2024.2389070

Source: https://arxiv.org/abs/2402.10842v4

The version-four PDF is https://arxiv.org/pdf/2402.10842v4 . Page numbers below
refer to that version. The journal version is AKCE International Journal of
Graphs and Combinatorics 22(1), 43–54.

## Source definitions

Section 1, p. 2:

> A paired dominating set of a graph G = (V, E) is a dominating set S ⊆ V such that the induced subgraph G[S] contains a perfect matching.

Definition 1.1, p. 2:

> A paired coalition in a graph G consists of two disjoint sets of vertices V₁ and V₂, neither of which is a paired dominating set but whose union V₁ ∪ V₂ is a paired dominating set.

Definition 1.2, p. 2:

> A paired coalition partition, abbreviated pc-partition, in a graph G is a vertex partition π = {V₁, V₂, . . . , Vₖ} such that every set Vᵢ of π is not a paired dominating set but forms a paired coalition with another set Vⱼ in π.

> The paired coalition number PC(G) equals the maximum order k of a pc-partition of G, and a pc-partition of G having order PC(G) is called a PC(G)-partition.

> As we will see later, not every graph G admits a pc-partition. In such situations we will say that PC(G) = 0.

Section 4.2, p. 9:

> A perfect binary tree is a binary tree in which all leaves have same distance to the root vertex.

> Given a perfect binary tree T, we call the distance between root vertex and each leaf, height of T.

> If T has height h, then we denote it by T(h).

## Conjecture 1

Conjecture 1, Section 4.2, p. 12, with the three displayed cases transcribed
in order:

> If T(h) is a perfect binary tree with height h, then PC(T(h)) = 5 if h = 2; 3 if h is odd; 0 otherwise.

The quantifier is over positive heights, root depth is zero, and heap label
r corresponds to Fin index r−1. A perfect matching in the induced subgraph
is represented by a matching subgraph of the original graph with exactly
the selected vertex set. The natural supremum of attained partition orders
is the maximum for finite graphs and is zero when there is no partition.

## Counterexample and scope

For height five put R = {1,8,9,10,11,12,13,14,15}. For each r in R, put
r and its two children in A, and put its four grandchildren in B₀,B₁,B₂,B₃
according to their labels 4r+j. The five part sizes are 27,9,9,9,9.
Odd cardinality excludes a perfect matching in each individual part.
A dominates; every A ∪ Bⱼ has a perfect matching obtained by matching r
to the child not adjacent to 4r+j and matching the other child to 4r+j.
Thus PC(T(5)) ≥ 5, contradicting the conjectured value three. This gives
a lower bound, not an exact value or a formally verified infinite family.

The same lower bound contradicts Lemma 4.10, p. 9, which states
PC(T(h)) ≤ 4 for h ≥ 3. The final remark on p. 12 says that to prove the
conjecture it remains to show PC(T(h)) ≠ 4 for h ≥ 5; excluding four does
not exclude a partition of order five. This counterexample does not
adjudicate the paper's independent results on other graph classes.

## Computed comparison

The experiment in the-omega-institute/trureturing-experiments, commit
`f4f5f6b6925228604ce8f8e805067a3fc7667a8c`, at
`docs/reports/samadzadeh-mojdeh-nadimi-2024-paired-coalition-binary-tree/check.py`
checks the explicit height-five partition and the block construction at
heights 2, 5 and 8. Running `python3 check.py` in that directory exits zero
with `RESULT PASS`. The part sizes are respectively (3,1,1,1,1),
(27,9,9,9,9) and (219,73,73,73,73). These are finite computations.
The program SHA-256 is
`89ff4366726353f026f6c90a61c4d8993730ab2f20bd508bf8b2f2726fb22ec3`;
the recorded output SHA-256 is
`23a53641028e5098a2c3037823f9c2262d55f972b0f83d3d3ca006ff5af53bbb`.

## Literature boundary

The source screen in issue #19217 checked version four, the publisher text,
arXiv:2409.10185, 2502.07310, 2509.15386 (versions one and two), and the
Henning–Mojdeh double-coalition papers. That inventory reports no settlement
of Conjecture 1. Completeness and currentness are ASSUMED-UNVERIFIED; the
formal counterexample does not establish literature priority.
