---
bibkey: pr39864subtreehelly
authors: 8e7; original file authors Kyle Miller and Rémi Bottinelli
year: 2026
title: "Helly property for subtrees of a tree (mathlib PR 39864)"
doi: null
url: https://github.com/8e7/mathlib4/tree/12cb0b6433584e454c4d4577472c4792f0dfe5c9
claim: "A nonempty finite indexed family of pairwise intersecting connected induced subgraphs of a tree has nonempty common intersection."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/SubtreeHelly
license: Apache-2.0
triage: anchor
---

# Native subtree Helly source

The source is mathlib PR 39864 at immutable revision `12cb0b6433584e454c4d4577472c4792f0dfe5c9`, authored by 8e7. The original Acyclic file credits Kyle Miller; Connectivity/Subgraph credits Kyle Miller and Rémi Bottinelli. The original copyright notices and Apache license are retained in the port and `docs/reports/licenses/mathlib-subtree-helly/LICENSE.txt`.

## Verified locator

https://github.com/8e7/mathlib4/tree/12cb0b6433584e454c4d4577472c4792f0dfe5c9

https://github.com/leanprover-community/mathlib4/pull/39864

## Source correspondence

All five selected declarations reside in `D5/S3/Combinatorics/Graph/Walks/SubtreeHelly.lean` under their original SimpleGraph names. `Connectivity/Subgraph.lean:581` supplies `preconnected_induce_iff_forall_exists_walk`. `Acyclic.lean:666`, `:680`, `:708`, and `:724` supply `IsTree.preconnected_induce_inter`, `IsTree.mem_walk_of_inter_nonempty`, `IsTree.inter_nonempty_of_pairwise_three`, and `IsTree.inter_nonempty_of_pairwise`, respectively. The first four are private consumed helpers; the finite-Finset endpoint is public. Their telescopes and proof bodies are unchanged. Only module/import/header and visibility packaging differs. This is an application of known external mathematics, not a claim of a new theorem.

The source toolchain is Lean 4.32.0-rc1. The host adopts Lean 4.35.0 and mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The received source uses these host definitions without changing the dependency pins.

## Common-source constraint fibers

For observation maps on one source space V, the feasibility set for each prescribed observation is its fiber in V. Equip V with one tree G and require each selected feasibility set to induce a connected graph in G. For a nonempty finite selection, pairwise compatibility means that every two fibers contain a common source vertex. Subtree Helly then yields one source vertex in all selected fibers. This concerns abstract readouts and their dependent fibers and finite common refinements. Pairwise relations on unrelated spaces, without connected feasibility subsets of one common source tree, do not meet these hypotheses.

## Scope and limits

The native endpoint quantifies over a nonempty Finset of indices and an unrestricted vertex type. It assumes induced Connected and pairwise nonempty intersections, and concludes a nonempty indexed intersection. IsTree and Connected include nonempty carriers. For a finite type of indices, Fintype.ofFinite and Finset.univ give the nonempty-index application; for an empty index type, IsTree.connected.nonempty supplies a vertex. The empty-family case uses exactly nonemptiness of the ambient vertex type. No finite ambient graph, median, gate, supplied tree-convexity, or common/triple-intersection certificate is a premise.

The transplant retires when the repository's own pinned mathlib contains an equivalent theorem: replace the port by direct upstream references then. Merging the upstream PR alone does not satisfy that condition.
