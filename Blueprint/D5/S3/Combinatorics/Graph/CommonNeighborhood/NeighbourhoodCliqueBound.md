# Neighbourhood-clique bound for common-neighbourhood energy

## Abstract

The neighbourhood-clique bound for the common-neighbourhood energy of every finite simple graph.

**Theorem 1.1 (The bound 4m - 2r).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(g, \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le 2 \cdot \sum_{v: V} \operatorname{max}\left(((\operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right):\mathbb{R}) - 1), 0\right) \land 2 \cdot \sum_{v: V} \operatorname{max}\left(((\operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right):\mathbb{R}) - 1), 0\right) = 4 \cdot (\operatorname{Finset}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(g\right)\right):\mathbb{R}) - 2 \cdot (\operatorname{Finset}.\operatorname{card}\left(\{v:V\mid 0 < \operatorname{SimpleGraph}.\operatorname{degree}\left(g, v\right)\}\right):\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

For every finite vertex type V and every simple graph g on V, the common-neighbourhood energy graphEnergy(g,commonNeighbour) is at most twice the sum over the vertices of max(d(v)-1,0), and that quantity equals 4m-2r, where m is the number of edges and r the number of vertices of positive degree. Isolated vertices and the empty graph are included; no connectivity or order hypothesis is present. This is Lemma 1 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996; the weaker bound 4m is prior work.

Let a_v be the indicator vector of the neighbourhood of v and d_v its size. Entrywise counting gives the common-neighbour matrix as A squared minus the degree diagonal, which is the sum over v of the outer product of a_v with itself minus the diagonal matrix of a_v. Put Pi_v for the outer product of a_v with itself divided by d_v, and zero when v is isolated. Then the summand for v is (d_v-1)Pi_v minus (diag a_v - Pi_v).

The matrix (d_v-1)Pi_v is a nonnegative multiple of an outer product, hence positive semidefinite. The matrix diag a_v - Pi_v is symmetric and idempotent, because a_v has entries 0 and 1 and a_v has squared length d_v, hence positive semidefinite. Summing over v writes the common-neighbour matrix as P-Q with both parts positive semidefinite. The energy of such a difference is at most tr P + tr Q, the positive-semidefinite difference bound of the noncentral commuting-graph module. Both traces equal the sum of max(d_v-1,0), and the handshake identity, that the degrees sum to 2m, gives 4m-2r.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.result`
- Dependency: [D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound](NoncentralBound.md)
