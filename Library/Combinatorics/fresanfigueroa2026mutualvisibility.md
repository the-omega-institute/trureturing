---
bibkey: fresanfigueroa2026mutualvisibility
authors: Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña
year: 2026
title: "Reconfiguration graphs of mutual-visibility sets"
doi: 10.48550/arXiv.2610.24324
url: https://arxiv.org/html/2610.24324v1
claim: "The question after Theorem 3.6 asks whether the full mixed reconfiguration graph of mutual-visibility sets is maximally connected for every connected host."
strata_touched:
  - D5/S3/Combinatorics/Graph/MutualVisibility/Model
  - D5/S3/Combinatorics/Graph/MutualVisibility/Geodesics
license: citation-only
triage: anchor
---

# Mixed reconfiguration of mutual-visibility sets

The primary source is arXiv:2610.24324v1. Section 2 defines a mutual-visibility
set by the existence, for each pair of distinct selected vertices, of a
shortest path in the original host whose internal vertices avoid the selected
set. The path may depend on the pair. Empty sets and all feasible ranks are
retained. Graphs are finite, simple, undirected and connected unless stated
otherwise.

Proposition 2.1 states that every subset of a mutual-visibility set is again
a mutual-visibility set. It attributes this hereditary property to
S. Cicerone, G. Di Stefano, L. Drožđek, J. Hedžet, S. Klavžar and I. G. Yero,
"Variety of mutual-visibility problems in graphs", Theoretical Computer
Science 974 (2023), 114096, DOI
[10.1016/j.tcs.2023.114096](https://doi.org/10.1016/j.tcs.2023.114096).
The attribution and bibliographic details are given in the primary source's
Proposition 2.1 and reference list.

Two distinct feasible sets are adjacent when their symmetric difference has
size one, or their two set differences are singletons whose vertices are
adjacent in the host. Thus token addition/removal and actual host-edge slides
are both present. Fixed-cardinality layers and slide-only token graphs are
different objects.

The question immediately after Theorem 3.6, repeated in Section 7, asks
whether the full reconfiguration graph is maximally connected for every
connected host: its vertex connectivity must equal its minimum degree.

The source's preceding order-at-least-three bound is not a hypothesis of
this question. Host orders one and two remain in scope. The finite separator
convention is that deleting a cut leaves at most one vertex or disconnects
the remaining induced graph. It gives connectivity zero for a singleton
complete graph and order minus one for every nonempty complete graph.

The formal model uses finite subsets and original-host shortest walks;
minimum-length walks are paths. Strict mandatory ancestry, used in the
rooted geometry, requires membership on every root geodesic. This auxiliary
relation is stronger than membership on some shortest path and does not
replace existential mutual visibility. The full connectivity equality is
proved by `D5/S3/Combinatorics/Graph/MutualVisibility/MinimumPair.result`,
using rooted comparability and simultaneous cut payments in addition to the
model and inward-replacement geometry. Its
[problem dossier](../../Problems/fresan-figueroa-goldfeder-lozano-2026-mutual-visibility-maximal-connectivity.md)
states the full conclusion and its fixed-layer boundary.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2610.24324
- Primary version: https://arxiv.org/html/2610.24324v1
