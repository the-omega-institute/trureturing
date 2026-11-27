---
slug: sheffield-xi-2025-conjecture-1
bibkey: sheffieldxi2025triangle
doi: 10.48550/arXiv.2507.14473
url: https://arxiv.org/abs/2507.14473v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result
---

# Sheffield–Xi Conjecture 1

## Problem

Nathan S. Sheffield and Zoe Xi ask in §1.1, Conjecture 1 of *Graphs With the Same Edge Count in Each Neighborhood*, arXiv:2507.14473v1, and repeat in §4:

> If there exists an $(r,c)$-triangle-regular graph, then there exists an $(r,c)$-triangle-regular abelian Cayley graph.

The introduction defines triangle regularity and §4 sets the finite abelian Cayley context. The finite, nonempty, simple graph convention follows the source's use of vertices, its simple-graph bounds and the scope recorded in the preregistration. https://arxiv.org/html/2507.14473v1#Thmconj1

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every pair of local counts | `∀ r c : ℕ`, including zero. |
| Existence of a finite nonempty simple undirected graph | `∃ (V : Type) (_ : Finite V) (_ : Nonempty V) (G : SimpleGraph V), …`. |
| Local counts at every vertex | `∀ v : V, Nat.card (G.neighborSet v) = r ∧ Nat.card (G.induce (G.neighborSet v)).edgeSet = c`. The edge set is unordered and the neighborhood is open. |
| An abelian Cayley graph realizing that same pair | `∃ (B : Type) (_ : Finite B) (instB : AddCommGroup B), letI : AddCommGroup B := instB; …`. The group order may be arbitrary. |
| Effective connection set | `∃ S : Set B, 0 ∉ S ∧ (∀ x ∈ S, -x ∈ S) ∧ triangleRegular (SimpleGraph.addCayley S) r c`. Neither the source claim nor this statement requires generation or connectivity. |
| Whole implication and its refutation | `claim : Prop` is the universal implication. The theorem's type is literally `Not claim`. |

## Motivation

The conjecture would let one study all realizable local-count pairs through finite abelian groups and the additive structure of their connection sets. The pair $(5,5)$ separates graph realization from abelian Cayley realization.

## Gap

Tier 1, source year 2025. The source has an explicit, recently proposed conjecture and a short route to an exact counterexample. The registered whole claim and the proposed $(5,5)$ route are recorded in issue #17356. The inspected Sheffield–Xi v1 original, the Caro–Mifsud preprint and journal version, the relevant *Flip colouring of graphs* sections, and Hak et al. v2 supply no whole all-abelian resolution in their inspected scope. Hak et al. repeat the conjecture. The antecedent witness and cyclic obstruction have published antecedents. https://github.com/the-omega-institute/trureturing/issues/17356

The original, the journal's Figure 5 and Theorem 6, and Hak et al.'s §4 and Appendix A give the source correspondence, the prior twelve-vertex planar witness, the cyclic scope, and the identification of the icosahedron. https://arxiv.org/html/2507.14473v1#S4 · https://doi.org/10.7151/dmgt.2551 · https://arxiv.org/html/2602.23517v2#Ax1

## Route

Take the icosahedral graph on two poles and two cyclic rings of five vertices. Every open neighborhood has five vertices and five edges.

For a zero-free symmetric connection set $S$, an oriented edge $x\to y$ in the zero neighborhood corresponds to $(x,y-x,-y)\in S^3$ of sum zero. The inverse sends $(a,b,c)$ to $(a,-c)$. Five edges would therefore yield ten ordered triples. Rotation modulo three counts the diagonal triples, one for each element killed by three. Negation on those nonzero elements has no fixed point, so their number is even. It is at most five and congruent to ten modulo three, so it equals four. The remaining element is its own negative and cannot occur in a zero-sum triple. Among the four elements killed by three a repeated coordinate forces a diagonal triple. Three distinct elements would contain an opposite pair and force the third element to be zero. Thus only four diagonal triples exist, contradicting ten.

## Falsifier

The exact witness must provide both local counts at all twelve vertices. A counterexample to the published implication also requires excluding every finite abelian Cayley realization of the pair. The proof applies the obstruction at the additive identity, with no size restriction on the ambient group in the obstruction and only finiteness of the connection set there.

## Evidence

The settling declaration is `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result`. The vertex type has twelve elements. The kernel checks that `icosahedronWitness` gives both local counts at every vertex, and `result` uses this certificate. The theorem `noCayleyFive` supplies the uniform obstruction. The dart–triple equivalence uses `CayleySquare.cayley_adj_iff` in both directions. The proof also uses Mathlib graph, dart, cardinality and permutation fixed-point results.

Sheffield and Xi authored the original conjecture. Caro and Mifsud supplied the published planar witness and the cyclic-only congruence, and Hak, Kozerenko, Lohvynov and Yarosh explicitly identify the icosahedron.

## Triage

`admission_basis: open-problem-resolution`. The refuted statement is the whole conjecture preregistered in #17356. The published small witness and the cyclic congruence carry prior attribution.

### What the settlement shows

- **Proved** by `D5/S3/Combinatorics/Graph/TriangleRegularity/SheffieldXiConjectureOne.result`. The pair $(5,5)$ occurs in a finite nonempty simple graph and has no abelian Cayley realization. The kernel checks the witness in `icosahedronWitness`; `noCayleyFive` derives the contradiction uniformly, including when the ambient abelian group is infinite and the connection set is finite.
- **Computed** by the bounded definition check. All 12 icosahedral local pairs are $(5,5)$ and the graph has 30 edges. For cyclic orders $6,8,10,12,18$, both dart maps and the obstruction were checked on respectively $1,3,6,10,28$ symmetric zero-free size-five sets. The kernel proof supplies the unbounded obstruction.
- **Proved in the literature**. Caro–Mifsud's cyclic restrictions apply to circulants. Sheffield–Xi's graph nonexistence interval in §3, abelian constructions in §4.1 and abelian nonexistence estimates in §4.2 follow from their stated arguments. Hak et al.'s compatible Turán families apply within their stated ranges. The conjecture would have transferred abelian nonexistence to arbitrary triangle-regular graphs, and the $(5,5)$ pair defeats that general transfer. https://doi.org/10.7151/dmgt.2551 · https://arxiv.org/html/2507.14473v1#S3 · https://arxiv.org/html/2602.23517v2#S4
- **Open here**. Classify the pairs that admit abelian Cayley realizations, identify hypotheses under which the transfer holds, and decide the unrestricted Cayley analogue allowing nonabelian groups. The existence of an analogous nonabelian spectral obstruction is a separate question from that realization analogue.

## ASSUMED-UNVERIFIED

Literature completeness beyond the inspected texts and indexes, unpublished work, unindexed or differently worded resolutions.
