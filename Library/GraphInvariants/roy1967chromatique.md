---
bibkey: roy1967chromatique
authors: Bernard Roy
year: 1967
title: "Nombre chromatique et plus longs chemins d'un graphe"
doi: 10.1051/m2an/1967010501291
url: https://www.numdam.org/item/M2AN_1967__1_5_129_0/
claim: "Every finite simple graph is k-colorable exactly when some edge orientation has every injective directed path bounded by k vertices."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/GallaiRoy
license: Apache-2.0
triage: anchor
---

# Finite graph colorings and directed paths

B. Roy, *Nombre chromatique et plus longs chemins d'un graphe*, Revue
française d'informatique et de recherche opérationnelle **1**(5) (1967),
129–132. [DOI](https://doi.org/10.1051/m2an/1967010501291).
The [original Numdam PDF](https://www.numdam.org/item/M2AN_1967__1_5_129_0.pdf)
contains Theorem 1 on page 129, its proof through page 131, and the
sharpness discussion immediately following that proof. A directed
"chemin élémentaire" counts all vertices, including endpoints. Theorem 1
bounds the chromatic number by the maximum such vertex count. Orienting
edges by increasing colors attains the bound. The stronger Theorem 2 is
outside this result. Roy's proof transforms a partition; the received
Lean proof below uses a maximal acyclic subrelation and is not claimed
to reproduce Roy's proof text.

The exact statement allows any finite vertex type in any universe,
any natural k, empty graphs, zero colors, reciprocal arcs, and cyclic
input relations. It asserts existence of a relation that covers every
edge in at least one direction and has no nonedge arcs. Paths are
injective functions Fin(m) to V with arcs at every consecutive index.
The singleton path explains the nonempty, zero-color boundary.

## Immutable Lean supplier and adaptation

Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
The selected software is Apache-2.0; this field describes the Lean
software, not a relicensing of Roy's paper.

The source is
[LeanPool/lean-pool@f5a146325cf5c14648a6a1c0897c3d78ce6ed889](https://github.com/LeanPool/lean-pool/blob/f5a146325cf5c14648a6a1c0897c3d78ce6ed889/LeanPool/ClassicalGraphColouring/Orientations/GallaiRoy.lean),
`LeanPool/ClassicalGraphColouring/Orientations/GallaiRoy.lean`.
Its source registry is `LeanPool/projects/classical-graph-colouring.yaml`
at that same immutable revision. The umbrella entry is
`jtraverso/galvin-dinitz@0aa98fc17e1e96ec408f7bad3198ce37a08d26fc`;
the registry specifically identifies the Gallai–Roy subsource as
[jtraverso/gallai-roy@e737218bf80c3d3684d670f5f8aa9a8257e1a52f](https://github.com/jtraverso/gallai-roy/tree/e737218bf80c3d3684d670f5f8aa9a8257e1a52f),
`GallaiRoyLib/GallaiRoy.lean`. These two source identities are distinct.
The registry records AI provenance and names Traverso Gianini as author.

The selected pooled source and host both pin Lean v4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. The original Gallai–Roy
source pins the earlier release candidate and is not the selected build
supplier. Dependency admission predicates remain open under SPEC A17;
this is an attributed leaf-source transplant under A17.2.

The receiver retains the source orientation and path definitions,
maximal-acyclic selection, longest-chain coloring, added-edge path
decomposition, and increasing-color construction. Pinned Mathlib chain
and pairwise APIs replace the elementary chain no-repetition proofs;
their unused reachability helper and the Lean Pool digraph bridge are
omitted. Both directional theorems are private and consumed by the sole
public equivalence. This is known mathematics and attributed source
reception, with no originality or exhaustive theorem-absence claim.

The complete, unmodified pooled distribution license and notice chain are:

- [pool LICENSE](../../docs/reports/ghrv-suppliers/pool-LICENSE.txt),
  SHA-256 `c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.
- [pool NOTICE](../../docs/reports/ghrv-suppliers/pool-NOTICE.txt),
  SHA-256 `d17b68e65d4242f88f3bd41eb8a58eba7e512b0d32edd197eb812ef69447fda1`.
- [pool NOTICE.extra.yml](../../docs/reports/ghrv-suppliers/pool-NOTICE.extra.yml.txt),
  SHA-256 `41b9d8eeedee68df9f184965d831c57b9d29f0ea9d3932517b84c7bdd8d81465`.
- [original Gallai–Roy LICENSE](../../docs/reports/ghrv-suppliers/gallai-roy-LICENSE.txt),
  SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.

The original Gallai–Roy and umbrella galvin-dinitz trees have LICENSE
and no NOTICE. Their LICENSE bytes agree; the last linked file preserves
both. The pooled NOTICE is preserved in full, including entries beyond
the selected leaf, without substituting a notice from another revision.

Retire this transplant when the host actually adopts a Mathlib revision
containing an equivalent complete finite orientation/coloring theorem,
after checking the orientation and path semantics and migrating consumers
to direct pinned applications and updating affected frozen records through
their lawful writer. Upstream acceptance alone does not meet this condition.

## Related restricted application

Section 15, especially Mathematical citation 15.10, of
[the native-alpha recut and memory volume](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
cites Roy for a specialized native menu/profile rank mechanism. That
application is a related reference, not the full arbitrary-finite-graph
GHRV equivalence, and none of its additional modeling premises is a
hypothesis of this theorem.
