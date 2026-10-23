# Stabilizer Even-Cycle Rank Correction

## Abstract

The actual character mask and generated root field give a rank correction of zero or two on every even-cycle component.

The original source family has odd n>=3, q>=2, any finite vertex type V (in particular Fin(N)), every symmetric zero-diagonal Gamma over F2, any coloring col:V->Fin(q) including empty parties, every character t:Fin(q-1)->ZMod(n), and every primitive nth root zeta in the algebraic closure of F2. RootField(zeta) is literally IntermediateField.adjoin F2 {zeta}. The proof only needs n nonzero and the given primitive-root property, so it retains the complete original family.

The translation delta(c)(i) is one when i=c and zero otherwise; the last party has the zero translation. The actual character readout is the dot product f_t(c)=sum_i t(i)delta(c)(i). partyPartition is its kernel equivalence relation. fibrePartition consists of its nonempty equivalence classes with the partition law. The mask is assigned piecewise: mask(Gamma,col,t)(u,v)=0 when the two colors lie in one actual fibre block, and otherwise it equals Gamma(u,v). A zero mask entry can also come from a different-block nonedge with Gamma(u,v)=0, so the zero value is not equivalent to common-block membership. The proof establishes that common-block membership is equivalent to equality of the original character readouts.

lambda(u)=zeta^f_t(col(u)), Lambda is its actual diagonal matrix, and M=Lambda Gamma+Gamma Lambda over the generated field. Primitive-root power injection proves lambda(u)=lambda(v) exactly when the character readouts agree. In characteristic two, the actual matrix entry is Gamma(u,v)(lambda(u)+lambda(v)); it is nonzero exactly on the actual masked graph. Because Gamma is F2-valued, every edge has Gamma(u,v)=1 and weight lambda(u)+lambda(v). edgeWeight bundles this nonzero value as a unit on edges; its default off the support is never traversed.

**Theorem 1.1 (The Actual Same-Component Correction).**

$$\forall data \in \mathrm{OriginalStabilizerData},\; \forall C \in \mathrm{ConnectedComponent}\left(\mathrm{maskedGraph}\left(data\right)\right),\; \forall k \in \mathrm{Nat},\; \forall z \in \mathrm{GraphIso}\left(\mathrm{cycleGraph}\left(\mathrm{mul}\left(2, \mathrm{add}\left(k, 2\right)\right)\right), \mathrm{ComponentGraph}\left(C\right)\right),\; (\mathrm{IsCycle}\left(\mathrm{componentCircuit}\left(data, C, z\right)\right)) \land ((\mathrm{length}\left(\mathrm{componentCircuit}\left(data, C, z\right)\right) = \mathrm{mul}\left(2, \mathrm{add}\left(k, 2\right)\right)) \land (\mathrm{IntRankDifference}\left(\mathrm{MRestricted}\left(data, C\right), \mathrm{MaskRestricted}\left(data, C\right)\right) = \mathrm{If}\left(\mathrm{alpha}\left(\mathrm{edgeWeight}\left(data\right), \mathrm{componentCircuit}\left(data, C, z\right)\right) = 1, 0, 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/MaskedCycles/StabilizerMaskedCycleRank.component_rank_difference_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C is an actual connected component of the actual masked graph, and z is any graph isomorphism from the ordinary cycle on L=2(k+2) vertices to C's induced graph. Thus every even length L>=4 and arbitrary cyclic labeling are retained. The parity isomorphism constructs the two alternating classes in this same component. componentCircuit is mapped through z and then through the actual component inclusion into the original masked graph. The theorem certifies that this is a simple cycle of length L.

Both principal matrices are restricted by the same subtype inclusion C->V. Their symmetry, exact support, and actual edge-entry correspondences are proved from the original data. The weighted restriction uses rank_even_cycle over RootField(zeta). The actual masked restriction is proved equal to the actual adjacency matrix of C's induced graph; rank_even_adjacency applies directly over F2. These two applications avoid any assumed extension-of-scalars bridge. All F2 edge entries are one, so the two adjacency matching products are both one and that actual masked restriction has rank L-2. The weighted restriction has rank L-2 or L according to equality of its actual matching products. This includes the ordinary F2 even-cycle adjacency specialization.

The public circuit_alpha computation is applied to the actual stabilizer edge units after the graph maps. Coercing the two unit products proves, without a supplied bridge, that the actual alpha equals one exactly when the two products of lambda(u)+lambda(v) agree. Subtracting the two actual ranks in the integers gives delta_C(t)=0 for alpha=1 and delta_C(t)=2 for alpha!=1. This is a conditional theorem of the stated graph-state model; it asserts no additional empirical premise. Weighted paths and odd cycles are handled by WeightedPathCycleRank and retain every nonzero characteristic-two edge weight.

The matrix-rank formulas with unit weights are established graph-theoretic results. The proof reuses NoEvenCycleRank.rank_eq_twice_maximum_matching for paths and odd cycles, the pinned rank and finite-dimensional APIs, and WeightedVertexProducts.alpha. Its new all-length inference is the cyclic transport kernel calculation in WeightedCycleKernel, followed by the actual support, reindexing and product correspondence above. No claim of literature novelty follows from a library search.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/MaskedCycles/StabilizerMaskedCycleRank.component_rank_difference_alpha`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk](../../../Combinatorics/Graph/Walks/WeightedCycleWalk.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank](../../../Combinatorics/Graph/Walks/WeightedPathCycleRank.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedVertexProducts](../../../Combinatorics/Graph/Walks/WeightedVertexProducts.md)
