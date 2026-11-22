---
slug: lao-2026-transversal-uniform-minor-question-7-0-2
bibkey: lao2026dynamicstransversal
doi: 10.48550/arXiv.2611.02586
url: https://arxiv.org/abs/2611.02586v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.has_uniform24_minor_iff
---

# Lao's graph criterion for a four-element uniform minor

## Problem

Hin Lon Lao, *Dynamics of Transversal Matroids*, Chapter 7, Question 7.0.2, printed p. 104 and PDF page 112, asks:

> Can we find a necessary and sufficient condition for a bipartite graph G such that T(G) contains U₂,₄ as a minor?

The following paragraph asks for a condition on the supplied graph and discusses the limitations of ordinary subgraph containment. The graph has a designated left side L, which is the whole ground of T(G), and a right side R, which indexes the presentation. Their independent types are finite and may be empty. An arbitrary edge relation A from L to R specifies the graph. [arXiv v1](https://arxiv.org/pdf/2611.02586v1#page=112) · [YorkSpace](https://hdl.handle.net/10315/44283)

## Motivation

Welsh's rank-flat criterion addresses the abstract matroid. Lao's Chapter 4 describes the behavior of actual graph presentations, including false positives for ordinary subgraph containment and an example where adding edges changes minor containment. A graph criterion must use the input presentation with its designated ground and all its edges. [Source note](../Library/FiniteGeometry/lao2026dynamicstransversal.md)

## Gap

The abstract existence of a U₂,₄ minor must be converted into a condition in the supplied graph. Contraction in the matroid can change which matching constraints remain relevant. A set of right vertices chosen from a few matchings would lose information about other edges of the original presentation.

## Route

Fix any left set X with |X| = 4. A native minor with ground exactly X relabels to U₂,₄ precisely when there exists a left set C disjoint from X such that the full neighborhood B of C ∪ X has size |C| + 2. For every two-element P ⊆ X there must be an edge-respecting bijection from C ∪ P onto B. The bijection may depend on P.

From a native contraction and deletion minor, take a basis K of the contracted set. Every K plus a pair in X is independent. Augmentation caps matchability in K ∪ X at |K| + 2. One universal dummy vertex still cannot make the entire set matchable, so Hall's theorem supplies a subset with deficiency at least two. Omitting any element of X would allow a restricted pair matching missing at most one vertex. Take C to be the deficient subset with X removed. The pair matchings force the exact neighborhood size and become bijections onto it.

Conversely, contract C and delete the remaining vertices outside X. A subset of X of size at most two extends to a matchable pair together with C. For a larger subset the full neighborhood is too small. The minor has ground X and the proof gives an actual ground equivalence to Fin 4 under which the native mapped matroid equals the rank-two uniform matroid. To recover the existential question, use the actual ground of a relabeled minor as X in the forward implication. A certificate for any four-element X gives a minor with that ground by the reverse implication.

## Falsifier

A finite bipartite graph and a specified four-element left set X would refute the equivalence if exactly one of the following held. A native U₂,₄ minor has ground X. The full-neighborhood certificate holds for X. The complete bipartite graph K₄,₄ presents a free matroid despite containing K₄,₂ as an ordinary subgraph. K₅,₃ presents U₃,₅ and has a U₂,₄ contraction, although every four-element set alone has three right neighbors. These examples exercise the full-neighborhood and contraction clauses.

## Evidence

The Lean declaration is `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.has_uniform24_minor_iff`. Its ground theorem includes all left vertices, and its independence theorem characterizes matchability for every finite left set, hence for every subset of a finite left side. This includes isolated vertices and allows empty sides. Hall's theorem is applied to the augmented graph on the forward implication. Bonin–Savitsky's graph-rank formula and Lao's circuit-neighborhood results give related deficiency tools. [Source note and related literature](../Library/FiniteGeometry/lao2026dynamicstransversal.md) · [Original question scope](https://github.com/the-omega-institute/trureturing/issues/32754#issuecomment-7061391051) · [Fixed-ground statement](https://github.com/the-omega-institute/trureturing/issues/32754#issuecomment-7062028024)

## Triage

| Item | Evidence and scope |
| --- | --- |
| Question 7.0.2 | **Proved by application of the fixed-ground Lean iff.** Existence of a minor is equivalent to existence of a four-element X meeting the certificate. The fixed-ground theorem is the sole resolution member. |
| Recognition on a finite explicitly supplied graph | **Derived in prose.** Enumerate disjoint C and X with X of size four, compute the full neighborhood, then check the six pair matchings onto it. A yes instance has a certificate comprising C, X and the six bijections. |
| Binary transversal recognition | **Derived in prose using Tutte's binary excluded-minor theorem.** The represented transversal matroid is binary exactly when the graph certificate is absent. |
| Further recognition bounds and patterns | **Open within this dossier.** There is no formal complexity bound for finding the certificate or deciding its absence. Other target minors and the adjoining questions in Chapter 7 are outside this settlement. |

## ASSUMED-UNVERIFIED

The primary full text of de Sousa–Welsh (1972), pp. 55–59, remains unread. Attributions from later work cover its known abstract classification. The bounded comparison supports no claim of global priority. [de Sousa–Welsh](https://doi.org/10.1016/0022-247X(72)90030-3)
