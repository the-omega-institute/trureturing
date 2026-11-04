# Separators and reachability in one surviving graph

## Abstract

Original-host mutual visibility and the auxiliary geometry of the full mixed reconfiguration graph.

**Theorem 1.1 (Connectivity is bounded by minimum degree).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.connectivity_le_minDegree`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.connectivity_le_minDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

For every finite nonempty simple graph, the separator connectivity is at most minimum degree.

**Theorem 1.2 (All smaller cuts give the reverse inequality).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.minDegree_le_connectivity`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.minDegree_le_connectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

If deleting every cut smaller than minimum degree leaves a preconnected graph, minimum degree is at most separator connectivity.

**Definition 1.3 (The entire original question).**

$$\mathrm{FullMaximalConnectivityClaim} \Leftrightarrow \left(\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{DecidableEq}\left(V\right)] [\mathrm{Nonempty}\left(V\right)] \forall H \in \mathrm{SimpleGraph}\left(V\right),\; \mathrm{Connected}\left(H\right) \Rightarrow \mathrm{vertexConnectivity}\left(\mathrm{reconfiguration}\left(H\right)\right) = \mathrm{minDegree}\left(\mathrm{reconfiguration}\left(H\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.FullMaximalConnectivityClaim` (`✓ std3`).

*Citation.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Every finite nonempty simple undirected connected host is quantified, including orders one and two. Its full original-geodesic visibility graph, with empty configurations, every rank, all single-label additions and removals, and all actual-host-edge slides, is asserted to have vertex connectivity equal to minimum degree. The minimum-pair separator argument proves this equality.

**Definition 1.4 (Reachability after one fixed deletion).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.CutReach`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.CutReach` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Both endpoints survive the given cut and are joined inside the actual induced graph after deleting that same cut.

**Theorem 1.5 (Extending a surviving path).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

A reachable endpoint can be extended across an actual graph edge whenever the next vertex survives the same fixed cut.

**Theorem 1.6 (A cut met by a two-edge escape).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_two_step_payment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_two_step_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

If one vertex is reachable in the surviving component and a two-edge path ends outside it, at least one of the next two vertices belongs to the given cut. Both edges and both payments concern one common graph and cut.

**Theorem 1.7 (A cut met by a finite chain).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_chain_payment`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_chain_payment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

Consecutive vertices along the stated finite index interval are adjacent. If its upper endpoint lies in the component or is cut and its lower endpoint lies outside the component, at least one indexed vertex is cut. The proof joins every uncut chain step and contradicts endpoint separation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.CutReach`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.FullMaximalConnectivityClaim`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.connectivity_le_minDegree`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_chain_payment`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.cutReach_two_step_payment`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity.minDegree_le_connectivity`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Model](Model.md)
