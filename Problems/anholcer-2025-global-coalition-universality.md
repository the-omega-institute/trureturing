---
slug: anholcer-2025-global-coalition-universality
bibkey: anholcer2025globalcoalitions
doi: null
url: https://arxiv.org/abs/2509.15386v4
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.result
---

# Global-coalition graph universality

## Problem

Anholcer, Besharati, Mojdeh and Samadzadeh, *Global coalitions in graphs*, arXiv:2509.15386v4, Section 7 Problem 58, PDF p. 29, asks whether every graph is realisable as a global coalition graph. The earlier alias is Besharati, Mojdeh and Samadzadeh, *Global coalition sets in graphs*, arXiv:2509.15386v1, Section 6 Problem 4, PDF p. 19. Both aliases identify one target.

### Original question and definitions

The following is the complete question and its conventions as recorded in preregistration [#23084](https://github.com/the-omega-institute/trureturing/issues/23084):

> The current complete question asks whether every finite simple undirected graph H of order at least two is isomorphic to the global coalition graph of some finite simple undirected host G of order at least two and some actual gc-partition of G. A gc-partition need not maximize the number of blocks. There is no connectedness, isolate-free, positive-edge-count or independent-block restriction.
>
> For the same vertex set, S dominates G precisely when every vertex is in S or adjacent to a member of S. Global domination means domination of both G and its genuine loopless complement. Two actual subsets A,B form a global coalition precisely when they are disjoint, neither is individually globally dominating, and their union globally dominates. The partition consists of nonempty pairwise-disjoint actual subsets covering all host vertices; every block has another distinct block in that same partition forming such a coalition. There is no singleton-dominating exception. The global coalition graph has these actual blocks as vertices and adjacency exactly the full global-coalition relation. Realization means genuine graph isomorphism.
>
> Current v4 places the order>=2 convention after Definition 2. V1 has no corresponding global lower-order restriction; its unrestricted full question is preserved separately, not silently narrowed. The proposed two-vertex witness obeys both versions and they count as one target. V3 withdrew v2 because it had been uploaded without consulting all authors and contained incorrect results; current v4 is restored and retains the question.

The formal claim is the literal closed assertion
$$
orall (V : Type) [operatorname{Finite}(V)], 2 le operatorname{Nat.card}(V) 	o
orall H : operatorname{SimpleGraph}(V),exists (W : Type) (_ : operatorname{Finite}(W)) (G : operatorname{SimpleGraph}(W)),2 le operatorname{Nat.card}(W) land
exists pi : operatorname{GCPartition}(G),operatorname{Nonempty}(operatorname{globalCoalitionGraph}(G,pi) simeq_g H).
$$

The model retains actual finite Type-valued target and host types, native simple graphs and native loopless complements, genuine `Setoid.IsPartition` nonempty/disjoint-cover structure, and a distinct actual coalition partner for every actual block. The v1 unrestricted-order alias is a source boundary, not a second theorem or credit.

## Motivation

The universal assertion includes the legal edgeless target on `Fin 2`. Every vertex of every global coalition graph has a distinct adjacent partner because the partition's `partners` field supplies an actual block forming a global coalition. The target therefore cannot be realized. The result settles the full current universality question while leaving the isolate-free target variant open.

## Gap

The preregistered target was an explicitly posed external problem. The bounded source and literature reading covered the v4 and v1 primary TeX/HTML definitions, the complete target passages, the v3 withdrawal and v4 restoration, and the ordinary, complementary, total, later ordinary, k-coalition and secure-coalition comparison boundaries. It did not establish worldwide citation completeness or priority. No exact prior settlement was found in the bounded indexed issue/PR and source scope; this dossier makes no originality or priority claim.

The formalization gap was to preserve the whole quantified target rather than replace it with a selected host, an independent-block partition, or an isolate-free restriction. The delivered `claim` keeps every target, host, graph, order, partition and native isomorphism quantifier.

## Route

The source note is [`Library/FiniteGeometry/anholcer2025globalcoalitions.md`](../Library/FiniteGeometry/anholcer2025globalcoalitions.md), with the v4 arXiv URL, v1 alias, TeX/PDF locators and comparison literature. The canonical Lean module is `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.lean`.

The module defines `GloballyDominating` using the existing `SimpleGraph.IsDominating` predicate on the graph and its native complement; `GlobalCoalition` with all four source clauses; `GCPartition` with actual blocks, `Setoid.IsPartition`, and a distinct actual partner; `globalCoalitionGraph` on the actual block subtype; and the literal closed `claim : Prop`. Its theorem `result : ¬ claim` invokes the private `no_edgeless_realization` lemma and the legal target `(⊥ : SimpleGraph (Fin 2))).

The obstruction applies to every host graph and every eligible actual partition. The target `Fin 2` has two vertices, so it meets the current v4 order bound and is also legal for the unrestricted v1 alias. The result does not assert a realization or classification theorem for isolate-free targets.

## Falsifier

The refutation would fail to address the source target if the original question excluded isolated target vertices, permitted a singleton-dominating exception, imposed independent or maximizing blocks, restricted the host family, or changed the global-complement convention. It would also fail if the formal `claim` omitted any target, host, order, partition or native-isomorphism quantifier.

The delivered model has no such restriction. A correction or later source version with a different domain would be a separate target. The isolate-free variant remains an open boundary.

## Evidence

The delivered module compiles with the current pinned Lean toolchain and its scoped report. The kernel result has literal type `Not claim`; the claim has literal type `Prop`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. No `sorry`, `native_decide` or new axiom is used.

The private helper `no_edgeless_realization` proves that every nonempty edgeless target is impossible for every host and actual partition. The public `result` specializes this obstruction to `Fin 2` and negates the complete universal claim. The nine public/model-field mirrors in the Scribe and generated Blueprint preserve the full telescopes and native names. The source and literature note is retained under its current registered path. No experiment or new program is needed.

## Triage

- **Proved — full current universality is refuted.** Kernel evidence: `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.result` has type `¬ claim`, where `claim` is the complete v4 order-at-least-two assertion above.
- **Proved — every-host obstruction.** Kernel evidence on the consumed private helper `D5/S3/Combinatorics/Graph/Domination/GlobalCoalitionUniversality.no_edgeless_realization`: for arbitrary host type, host graph and actual `GCPartition`, no nonempty edgeless target admits a native graph isomorphism from the global coalition graph. The public result uses this helper.
- **Proved in the formal explanation — legal nonempty edgeless family.** The helper's quantified target type is arbitrary subject only to `Nonempty`; hence every finite nonempty edgeless target is obstructed. The delivered public theorem instantiates only `Fin 2`; the family statement is explanatory prose, not an additional Lean declaration.
- **Open — isolate-free global universality.** The delivered result gives no realization construction or classification for targets with no isolated vertices.
- **Proved in the model and source correspondence — actual partition requirements.** `GCPartition.isPartition` preserves nonempty, pairwise-disjoint covering blocks, and `GCPartition.partners` supplies a distinct actual partner for every block. The graph vertices are the actual block subtype and adjacency is the complete global-coalition predicate.
- **Literature reading — model boundaries.** Ordinary coalition universality permits singleton-dominating blocks; complementary-coalition work studies a different ordinary-complement relation; total-coalition realizability assumes an isolate-free target and total domination; later ordinary, k-coalition and secure-coalition results use distinct predicates. These comparisons do not settle the present global target.
- **Open — worldwide literature completeness and priority.** The bounded primary-source and indexed issue/PR reading does not certify exhaustive citation coverage or priority.

## ASSUMED-UNVERIFIED

Worldwide literature completeness, citation-index coverage and priority remain ASSUMED-UNVERIFIED. The isolate-free realization problem and any corrected or strengthened universality statement remain open. These limits do not weaken the kernel refutation of the literal v4 target.
