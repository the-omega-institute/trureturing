# Peak transport in a retained forest

## Abstract

Reassembling the conflict components turns peaks into vertices without retained children.

**Theorem 1.1 (Count transport for marked trees).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (r: V), \forall (S: \operatorname{ForestSample}\left(V\right)), \operatorname{card}\left(\operatorname{PeakSet}\left(\operatorname{retained}\left(S\right)\right)\right) = \operatorname{card}\left(\operatorname{NoRetainedChildSet}\left(\operatorname{tree}\left(\operatorname{forestEquiv}\left(r\right)\left(S\right)\right), \operatorname{retained}\left(\operatorname{forestEquiv}\left(r\right)\left(S\right)\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

The sample consists of a tree and a spanning subgraph obtained by retaining some edges. Each component is rooted at its entry vertex on paths from the ambient root. Replace its tree by the fixed-root image and leave all intercomponent edges in place. This relates its original peak count to the number of vertices with no retained child in the new rooted tree.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler](CentralScheduler.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates](RootedCoordinates.md)
