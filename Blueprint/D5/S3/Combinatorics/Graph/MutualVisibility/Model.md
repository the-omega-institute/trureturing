# The source model and separator conventions

## Abstract

Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.

**Definition 1.1 (Equality of configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationDecidableEq`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationDecidableEq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Classical equality on the subtype of feasible finite subsets supports the finite cut interface.

**Definition 1.2 (Mutual visibility in the original host).**

$$\forall V \in \mathrm{Type},\; \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall S \in \mathrm{Finset}\left(V\right),\; \mathrm{Visible}\left(H, S\right) \Leftrightarrow \left(\forall u \in V,\; u \in S \Rightarrow \left(\forall v \in V,\; v \in S \Rightarrow \left(u \ne v \Rightarrow \left(\exists p \in \mathrm{Walk}\left(H, u, v\right),\; \mathrm{length}\left(p\right) = \mathrm{dist}\left(H, u, v\right) \land \left(\forall z \in V,\; \left(z \in \mathrm{support}\left(p\right) \land z \in S\right) \Rightarrow \left(z = u \lor z = v\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Visible` (`✓ std3`).

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For every pair of distinct selected endpoints there exists a shortest walk in the original host, and any selected vertex on its support is an endpoint. A minimum-length walk is a path, so this is the source geodesic definition. The chosen path may differ between endpoint pairs.

**Definition 1.3 (Both source move rules).**

$$\forall V \in \mathrm{Type},\; [\mathrm{DecidableEq}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \forall S \in \mathrm{Finset}\left(V\right),\; \forall T \in \mathrm{Finset}\left(V\right),\; \mathrm{MixedMove}\left(H, S, T\right) \Leftrightarrow \left(S \ne T \land \left(\mathrm{card}\left(\mathrm{symmDiff}\left(S, T\right)\right) = 1 \lor \left(\exists x \in V,\; \exists y \in V,\; \mathrm{sdiff}\left(S, T\right) = \mathrm{singleton}\left(x\right) \land \left(\mathrm{sdiff}\left(T, S\right) = \mathrm{singleton}\left(y\right) \land \mathrm{Adj}\left(H, x, y\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.MixedMove` (`✓ std3`).

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Distinct finite sets are joined by one-vertex symmetric difference, or by singleton set differences whose removed and inserted labels are adjacent in the actual host. The latter label is unoccupied before the slide. No fixed rank or unrestricted token swap is substituted.

**Definition 1.4 (The complete feasible family).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Configuration`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Configuration` (`✓ std3`).

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

A configuration is a finite subset together with its mutual-visibility proof. The empty set, every feasible rank, and both small host orders are retained.

**Definition 1.5 (The full mixed graph).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfiguration`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfiguration` (`✓ std3`).

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Vertices are all configurations and adjacency is exactly MixedMove. Symmetry comes from undirected host adjacency and from symmetric difference; distinct endpoints exclude loops.

**Definition 1.6 (Finiteness of the configuration family).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationFintype`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationFintype` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For a finite host, all configurations form a finite subtype of the finite powerset.

**Definition 1.7 (Decidable finite adjacency).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfigurationDecidableAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfigurationDecidableAdj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Classical decidability supplies the finite-graph degree interface without replacing the mathematical move predicate.

**Theorem 1.8 (Hereditary visibility).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_mono` (`✓ std3`). ∎

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Proposition 2.1 of Fresán-Figueroa, Goldfeder and Lozano-Piña states hereditary mutual visibility and attributes it to Cicerone et al. (2023), Variety of mutual-visibility problems in graphs. A geodesic avoiding the other vertices of a larger selected set also avoids the other vertices of each selected subset.

**Theorem 1.9 (The empty configuration).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

The endpoint condition is vacuous for the empty set. It is present in the graph.

**Theorem 1.10 (Singleton configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_singleton`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

There are no distinct selected endpoints in a singleton.

**Theorem 1.11 (All pairs of a connected host).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Connectedness supplies a shortest original-host walk. A selected pair has no third selected label to avoid.

**Theorem 1.12 (Token addition).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Inserting a previously unoccupied label changes the symmetric difference by precisely that one label.

**Theorem 1.13 (Token removal).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_erase`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_erase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Erasing an occupied label is the reverse of its insertion.

**Definition 1.14 (Finite vertex separators).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Separates`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Separates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

A cut either leaves at most one vertex or makes the induced graph on all surviving vertices fail to be preconnected. The remaining graph is the actual induced graph, with both move types preserved.

**Definition 1.15 (Vertex connectivity with complete-graph conventions).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.vertexConnectivity`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Model.vertexConnectivity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Take the least cardinality of a separator. The whole vertex set always supplies a candidate. On a nonempty complete graph this convention gives its order minus one, and on a one-vertex graph it gives zero. The minimum-pair separator argument proves the matching lower bound for the full visibility graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Configuration`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.MixedMove`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Separates`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.Visible`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationDecidableEq`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.configurationFintype`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_erase`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.mixedMove_insert`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfiguration`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.reconfigurationDecidableAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.vertexConnectivity`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_empty`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_mono`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_pair`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Model.visible_singleton`
