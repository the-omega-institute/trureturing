---
bibkey: anholcer2025globalcoalitions
authors: Marcin Anholcer; Nazli Besharati; Doost Ali Mojdeh; Mohammad Reza Samadzadeh
year: 2025
title: Global coalitions in graphs
doi: null
url: https://arxiv.org/abs/2509.15386v4
claim: Section 7 Problem 58 asks whether every graph is realizable as the global coalition graph of an actual global coalition partition.
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality
license: citation-only
triage: anchor
---

# Global coalition realizability

## Verified locator

- Current source: https://arxiv.org/abs/2509.15386v4
- Current TeX: https://arxiv.org/src/2509.15386v4
- Current PDF: https://arxiv.org/pdf/2509.15386v4
- Earlier alias: https://arxiv.org/abs/2509.15386v1
- Earlier TeX: https://arxiv.org/src/2509.15386v1
- Earlier PDF: https://arxiv.org/pdf/2509.15386v1
- Submission history: https://arxiv.org/abs/2509.15386
- Withdrawal notice: https://arxiv.org/abs/2509.15386v3
- Ordinary coalition graphs, DOI 10.22049/CCO.2022.27916.1394:
  https://comb-opt.azaruniv.ac.ir/article_14431_a7f093b82d7cfb1bf521fdf78f7dd886.pdf
- Complementary coalition graphs, DOI 10.7151/dmgt.2565:
  https://www.dmgt.uz.zgora.pl/publish/pdf.php?doi=2565
- Total coalitions: https://arxiv.org/pdf/2301.09979v3
- Later ordinary coalitions: https://arxiv.org/pdf/2511.21112v1
- k-coalitions: https://arxiv.org/abs/2608.05403v1
- Secure coalitions: https://arxiv.org/abs/2511.21170v2

## Source and version boundaries

Version four is titled *Global coalitions in graphs* and has the four authors
listed above. Section 1.1, PDF pp. 2–3, defines the material graph and partition
notions. Section 7 Problem 58, PDF p. 29, contains the complete question.
The source file `version2_new_MA.tex` has SHA-256
`ed0627f8021cff18edf57ede9cf0f77f9f8168fc6803fb062d9cb29479aed4c3`;
its material anchors are lines 89, 109, 115, 127, 132–141 and 2930–2933.

Version one, by Besharati, Mojdeh and Samadzadeh, is titled *Global coalition
sets in graphs*. Section 6 Problem 4, PDF p. 19, is the earlier alias of the
same question. Its `Paper.tex` has SHA-256
`d1e72bd3fe07a931786f82fa218952b7f9eba3d33283fef157fce9e5fcd09673`;
the whole question is at lines 2841–2847. It has no corresponding global
order-at-least-two assumption. These are one question with distinct domain
boundaries, rather than two independent results.

The submission history identifies v4 as the current restored version. The v3
withdrawal notice concerns v2: it says that v2 was uploaded without consulting
all authors and contains incorrect results. The restored v4 still prints the
question. This does not certify other statements in v4 or literature priority.

## Exact definitions and whole question

The graphs are simple, finite and undirected. Domination means that each
vertex belongs to the set or has a neighbour in it. The native complement
has the same vertex set, excludes loops, and reverses adjacency on distinct
vertices. A globally dominating set dominates both graphs.

Definition 1 requires four clauses for a global coalition: the actual subsets
A and B are disjoint, A is not globally dominating, B is not globally
dominating, and their union is globally dominating. Definition 2 requires a
vertex partition in which each class is not globally dominating and has
another class forming an actual global coalition. Its following paragraph
excludes exceptional singleton globally dominating classes and assumes
order at least two for the remainder of the paper.

The question itself says:

> For any graph G and any gc-partition pi of G, we can define the global
> coalition graph GCG(G,pi), whose vertices correspond bijectively to the
> elements of pi. Two vertices are adjacent in GCG(G,pi) if and only if their
> corresponding subsets in pi together form a global coalition in G.
> This leads to the following question: Is every graph realisable as a global
> coalition graph?

In full v4 quantification, every finite target H of order at least two is to
have some finite host G of order at least two and some gc-partition pi with
GCG(G,pi) isomorphic to H. All eligible partitions are allowed: neither
independent blocks nor a maximum number of blocks is required. No
connectedness, isolate-free-target or positive-edge restriction is present.

## Model correspondence and obstruction

`GloballyDominating` reuses the existing `SimpleGraph.IsDominating` in G
and its native complement. `GlobalCoalition` contains all four clauses.
`GCPartition.blocks` is a set of actual subsets; `Setoid.IsPartition` excludes
the empty set and gives unique covering membership for each vertex.
`GCPartition.partners` supplies an actual distinct member of those same
blocks satisfying the complete coalition predicate. Vertices of
`globalCoalitionGraph G pi` are the subtype of members of pi.blocks, and its
native SimpleGraph adjacency is precisely that predicate. Symmetry uses
symmetric disjointness and union commutativity; a loop would both make A
and fail to make A globally dominating, since A union A is A.

The closed `claim : Prop` uses arbitrary V : Type with Finite V and
2 <= Nat.card V, arbitrary H : SimpleGraph V, and an existential arbitrary
W : Type with Finite W, G : SimpleGraph W, 2 <= Nat.card W, pi : GCPartition G
and Nonempty (globalCoalitionGraph G pi isomorphic to H). It imposes no
finite-label or host-family restriction. The model definitions and private
obstruction lemma also allow arbitrary universe levels.

The legal target is the edgeless native SimpleGraph on Fin 2. For every host
and every actual gc-partition, each block has a distinct coalition partner,
which is an actual neighbour in its global coalition graph. Under a proposed
isomorphism to the target, take the preimage of target vertex zero and its
partner; adjacency transport would produce an edge in an edgeless graph.
The private `no_edgeless_realization` establishes this obstruction for every
host and every nonempty edgeless target. `result : Not claim` applies it to
Fin 2, thereby negating the entire displayed universal assertion. The same
argument excludes this target under the unrestricted v1 question. Whether
every isolate-free target is globally realizable remains unsettled here.
No conclusion is asserted about the paper's other theorems.

## Related results and limits of transfer

Haynes et al., *Coalition graphs*, Theorem 1, pp. 426–428, realizes every
ordinary target, but ordinary coalition partitions allow singleton dominating
classes. Its construction uses singleton universal host vertices to implement
target isolates. Those classes do not provide global coalition partners.
For the two singleton blocks of K2, the ordinary coalition graph is edgeless,
whereas the global coalition graph is K2 because each singleton fails to
dominate the native edgeless complement and their union is all vertices.
Thus ordinary universality does not transfer to the global predicate.

Bakhshesh and Henning, *Complementary coalition graphs: characterization and
algorithm*, Proposition 2 and Theorem 5, pp. 915–919, study ordinary coalition
graphs isomorphic to the complement of their host. The complement is the
output comparison graph; their coalition predicate still uses ordinary
domination only. This does not supply simultaneous domination in the host
and its complement.

Barat and Blazsik, arXiv:2301.09979v3, Lemma 2.5, realizes every isolate-free
target as a total coalition graph. Total domination requires neighbours even
for vertices inside the set. Its target restriction excludes the edgeless
Fin 2 graph, and its predicate is different from global domination.
The full vertex set of an edgeless two-vertex graph globally dominates but
does not totally dominate. A two-vertex subset of K3 totally dominates but
fails to dominate the native complement.

The later ordinary result in arXiv:2511.21112v1 retains the singleton
exception. The k-coalition result in arXiv:2608.05403v1 uses k-domination and
allows exceptional dominating blocks of size k. The secure-coalition result
in arXiv:2511.21170v2 has an isolate-free target hypothesis and a defender
condition. None of these statements supplies the complete global claim or
its negation by a demonstrated equivalence.

The material source scope is the v1/v4 introductory definitions, whole
questions and relevant global assumptions, with complete-TeX assumption
searches; it is not a verification of all proofs in either paper. The related
source scope is the displayed definitions and realizability results above,
including the ordinary and total constructions; the later papers were not
read cover to cover. No equal-or-stronger global settlement was identified
in that bounded scope. Literature completeness, citation-list coverage and
priority remain ASSUMED-UNVERIFIED; unavailable citation-index results do
not certify originality. The elementary argument is an application of the
partition's partner requirement, not a claim of a new graph-theoretic method.

The imported domination definition retains its source attribution and
Apache-2.0 notice in GraphCoverDomination. This note is citation-only and
does not copy an external proof implementation.
