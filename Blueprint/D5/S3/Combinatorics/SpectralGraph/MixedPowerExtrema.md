# Mixed spectral extrema of distance powers

## Abstract

The path and the complete graph attain the two mixed spectral extrema over all finite connected simple graphs of a given order.

**Theorem 1.1 (The lower and upper extrema with equality).**

$$\forall (V : \operatorname{Type} u), \forall [\operatorname{Fintype}\left(V\right)], \forall [\operatorname{DecidableEq}\left(V\right)], \forall (G : \operatorname{SimpleGraph}\left(V\right)), (\operatorname{SimpleGraph.Connected}\left(G\right)) \to \forall (k : \operatorname{Nat}), (1 \le k) \to \forall (\alpha : \mathbb{R}), (0 \le \alpha) \to (\alpha < 1) \to (\operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(\operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right), k\right), \alpha\right) \le \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right), \alpha\right) \land (\operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right), \alpha\right) \le (\operatorname{Fintype.card}\left(V\right) : \mathbb{R}) - 1 \land ((\operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right), \alpha\right) = \operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(\operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right), k\right), \alpha\right) \iff (\operatorname{Fintype.card}\left(V\right) \le k + 1 \lor \operatorname{Nonempty}\left(\operatorname{SimpleGraph.Iso}\left(\operatorname{SimpleGraph.pathGraph}\left(\operatorname{Fintype.card}\left(V\right)\right), G\right)\right))) \land (\operatorname{OmegaMath.MixedAdjacency.mixedTop}\left(\operatorname{D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation.graphPower}\left(G, k\right), \alpha\right) = (\operatorname{Fintype.card}\left(V\right) : \mathbb{R}) - 1 \iff \forall (i : V), \forall (j : V), \operatorname{SimpleGraph.dist}\left(G, i, j\right) \le k))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MixedPowerExtrema.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joyentanuj Das; Anto Jerrin Ashni R; Sangeetha C (2026). *Extremal adjacency and distance spectral radii of graph powers*. DOI: [10.48550/arXiv.2611.29397](https://doi.org/10.48550/arXiv.2611.29397). URL: <https://arxiv.org/abs/2611.29397v1>.

*Commentary.*

Question 5.1 in Das–Ashni–Sangeetha, arXiv:2611.29397v1, printed p. 17, asks for the extrema of the largest eigenvalue of the mixed degree–adjacency matrix of a graph power. Both matrices use the power graph. The existing graphPower joins distinct vertices at base distance at most k on connected graphs. The OmegaMath theorem mixedTop_isGreatest identifies mixedTop with the greatest element of the real matrix spectrum.

A spanning tree reduces the lower bound to trees. Reflected coordinates compare the edge energies under a terminal-leaf transfer, and a sum of rooted distance deficits gives a finite descent to a path. The last transfer is strict for a nonpath tree above the complete-power range. A chord on a spanning path gives an extra power edge. For the upper equality, strict spectral monotonicity and the complete graph's row sum identify exactly the complete powers.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MixedPowerExtrema.result`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/TreePathCuts](../Graph/LinearForests/TreePathCuts.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/MixedPowerGraft](MixedPowerGraft.md)
