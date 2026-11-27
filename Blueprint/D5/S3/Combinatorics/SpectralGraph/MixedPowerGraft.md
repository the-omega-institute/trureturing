# Terminal-leaf transfers for powered graphs

## Abstract

A terminal-leaf transfer weakly decreases the mixed largest eigenvalue. The final transfer to a path is strict under the stated hypotheses.

**Theorem 1.1 (Power adjacency).**

$$\forall (V : \operatorname{Type} u), \forall (G : \operatorname{SimpleGraph}\left(V\right)), (\operatorname{SimpleGraph.Connected}\left(G\right)) \to \forall (k : \operatorname{Nat}), \forall (i : V), \forall (j : V), \operatorname{SimpleGraph.Adj}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right), i, j\right) \iff i \neq j \land \operatorname{SimpleGraph.dist}\left(G, i, j\right) \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.graphPower_adj_dist_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

On a connected graph, extended distance agrees with the natural-valued shortest-path distance.

**Theorem 1.2 (Connected powers).**

$$\forall (V : \operatorname{Type} u), \forall (G : \operatorname{SimpleGraph}\left(V\right)), (\operatorname{SimpleGraph.Connected}\left(G\right)) \to \forall (k : \operatorname{Nat}), (1 \le k) \to \operatorname{SimpleGraph.Connected}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.graphPower_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

Every edge of the original graph is present in each positive power.

**Theorem 1.3 (Weak comparison for pendant arms).**

$$\forall (V : \operatorname{Type} u), \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (z : V), \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(T\right)\right)], \forall (a : \operatorname{Nat}), \forall (b : \operatorname{Nat}), \forall (X : \operatorname{OmegaMath.TreeGraft.PendantArm}\left(T, z, a\right)), \forall (Y : \operatorname{OmegaMath.TreeGraft.PendantArm}\left(T, z, b\right)), \forall [\operatorname{DecidableEq}\left(V\right)], (\operatorname{SimpleGraph.IsTree}\left(T\right)) \to \forall (hb : 1 \le b), \forall (hab : b \le a), (\operatorname{OmegaMath.TreeGraft.PendantArm.first}\left(X, \operatorname{LE.le.trans}\left(hb, hab\right)\right) \neq \operatorname{OmegaMath.TreeGraft.PendantArm.first}\left(Y, hb\right)) \to \forall (k : \operatorname{Nat}), (1 \le k) \to \forall (\alpha : \mathbb{R}), (0 \le \alpha) \to (\alpha \le 1) \to \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(\operatorname{OmegaMath.TreeGraft.PendantArm.move}\left(X, Y, hb\right), k\right), \alpha\right) \le \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(T, k\right), \alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_move_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

Reflect coordinates on the path between the two attachment points. Pair and off-path energy comparisons preserve the Rayleigh bound.

**Theorem 1.4 (Strict final transfer for powers at least two).**

$$\forall (V : \operatorname{Type} u), \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (z : V), \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(T\right)\right)], \forall (a : \operatorname{Nat}), \forall (b : \operatorname{Nat}), \forall (X : \operatorname{OmegaMath.TreeGraft.PendantArm}\left(T, z, a\right)), \forall (Y : \operatorname{OmegaMath.TreeGraft.PendantArm}\left(T, z, b\right)), \forall [\operatorname{DecidableEq}\left(V\right)], (\operatorname{SimpleGraph.IsTree}\left(T\right)) \to \forall (hb : 1 \le b), \forall (hab : b \le a), (\operatorname{OmegaMath.TreeGraft.PendantArm.first}\left(X, \operatorname{LE.le.trans}\left(hb, hab\right)\right) \neq \operatorname{OmegaMath.TreeGraft.PendantArm.first}\left(Y, hb\right)) \to (\neg\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(T, \operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right)\right)\right)) \to (\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(\operatorname{OmegaMath.TreeGraft.PendantArm.move}\left(X, Y, hb\right), \operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right)\right)\right)) \to \forall (k : \operatorname{Nat}), (2 \le k) \to (k + 2 \le \operatorname{Fintype.card}\left(V\right)) \to \forall (\alpha : \mathbb{R}), (0 \le \alpha) \to (\alpha < 1) \to \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(\operatorname{OmegaMath.TreeGraft.PendantArm.move}\left(X, Y, hb\right), k\right), \alpha\right) < \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(T, k\right), \alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_last_move_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

A fixed off-path incidence in the old power is missing from the path power. Its mixed energy is strictly positive on a positive maximizing vector.

**Theorem 1.5 (Strict final transfer for the first power).**

$$\forall (V : \operatorname{Type} u), \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall (T : \operatorname{SimpleGraph}\left(V\right)), \forall (z : V), \forall (L : \operatorname{Nat}), \forall [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(T\right)\right)], \forall (A : \operatorname{OmegaMath.TreeGraft.TerminalArms}\left(T, z, L\right)), (\operatorname{SimpleGraph.IsTree}\left(T\right)) \to (\neg\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(T, \operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right)\right)\right)) \to (\operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(\operatorname{OmegaMath.TreeGraft.graft}\left(T, z, \operatorname{Subtype.val}\left(\operatorname{OmegaMath.TreeGraft.TerminalArms.q}\left(A, \operatorname{Fin.last}\left(L\right)\right)\right)\right), \operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right)\right)\right)) \to \forall (\alpha : \mathbb{R}), (0 \le \alpha) \to (\alpha < 1) \to \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(\operatorname{OmegaMath.TreeGraft.graft}\left(T, z, \operatorname{Subtype.val}\left(\operatorname{OmegaMath.TreeGraft.TerminalArms.q}\left(A, \operatorname{Fin.last}\left(L\right)\right)\right)\right), 1\right), \alpha\right) < \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(T, 1\right), \alpha\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_last_graft_one_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

If the top values agree, both vectors satisfy their maximizing eigenvector equations. For the three possible orders of the attachment coordinates, the moved leaf row, opposite-arm row, and old attachment row give contradictions, respectively.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.graphPower_adj_dist_iff`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.graphPower_connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_last_graft_one_lt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_last_move_lt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft.mixedTop_move_le`
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation](../Graph/ZeroForcing/GridPowerZeroForcingRefutation.md)
