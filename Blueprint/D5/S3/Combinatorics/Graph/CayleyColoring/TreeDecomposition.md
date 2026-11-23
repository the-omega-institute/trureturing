# Peaks and leaves of a native rooted tree

## Abstract

A fixed-root bijection sends peaks to leaves in cardinality.

**Theorem 1.1 (Peak and rooted-leaf counts).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (r: V), \forall (T: \operatorname{Tree}\left(V\right)), \operatorname{filterCard}\left(\operatorname{Peak}\left(\operatorname{graph}\left(T\right)\right)\right) = \operatorname{filterCard}\left(\operatorname{RootedLeaf}\left(\operatorname{graph}\left(\operatorname{fixedRootEquiv}\left(r\right)\left(T\right)\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard` (`✓ std3`). ∎

*Citation.* Georg Seitz (2011). *Analysis of various parameters in labelled trees and tree-like structures*. URL: <https://repositum.tuwien.ac.at/handle/20.500.12708/10695>.

*Commentary.*

A peak has no greater-labeled neighbor. A rooted leaf has no adjacent vertex farther from the root. The equivalence removes the least label, recursively replaces the attached branches, and relabels the pivot to the specified root. Seitz gives the peak-to-leaf bijection in Corollary 5.2.2 and §5.3.1.2, and de Panafieu et al. use its distributional consequence in Proposition 5.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard`
