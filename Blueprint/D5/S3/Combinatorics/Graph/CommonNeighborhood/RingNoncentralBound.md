# Common-neighbourhood energy of the noncentral commuting graph of a ring

## Abstract

The strict common-neighbourhood energy bound for the commuting graph of every finite noncommutative ring.

**Definition 1.1 (The center).**

$$\operatorname{ringCenter}\left(R\right) = \{x\mid \forall y \in R,\; x \cdot y = y \cdot x\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.ringCenter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Acknowledgement.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

ringCenter(R) is the set of elements commuting with every element of R. For an associative ring this is the usual center.

**Definition 1.2 (Individual noncentral vertices).**

$$\operatorname{Vertex}\left(R\right) = \{x:R\mid \neg x \in \operatorname{ringCenter}\left(R\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Acknowledgement.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

Vertex(R) is the subtype of elements outside the center; vertices are individual elements.

**Definition 1.3 (The commuting graph).**

$$\forall x \in \operatorname{Vertex}\left(R\right),\; \forall y \in \operatorname{Vertex}\left(R\right),\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{commutingGraph}\left(R\right), x, y\right) \Leftrightarrow \left(x \ne y \land x \cdot y = y \cdot x\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.commutingGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Acknowledgement.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

Two distinct noncentral elements are adjacent exactly when their two products in R are equal.

**Theorem 1.4 (The strict bound).**

$$\forall R \in \operatorname{Type},\; [\operatorname{NonUnitalRing}\left(R\right)][\operatorname{Fintype}\left(R\right)]\left(\exists a \in R,\; \exists b \in R,\; a \cdot b \ne b \cdot a\right) \Rightarrow \left(1 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) \land \left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) + 2 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right) \land \left(3 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right) \land \left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{commutingGraph}\left(R\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \land \left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \le (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2) \land (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2) < 2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - 1) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - 2)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

For every finite associative ring R, not assumed unital and with no commutative-centralizer hypothesis, that has two elements whose products differ, write z for the order of the center and n for the number of noncentral elements. Then z is at least 1, n is at least z+2, hence at least 3, and the common-neighbourhood energy of commutingGraph(R) is at most n max(n-z-4,0), which is at most n(n-z-2), which is strictly below the complete-graph value 2(n-1)(n-2). The bound n(n-z-2) < 2(n-1)(n-2) is Corollary 3 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996; the factor max(n-z-4,0) sharpens it through the neighbourhood-clique bound.

For a noncentral x, the elements commuting with x form an additive subgroup, because multiplication distributes over addition and negation. It is proper since x is noncentral, so its index is at least two and it has at most half of the elements of R. It contains the center, x itself and every graph neighbour of x, and these three parts are disjoint. Hence deg(x)+z+1 is at most |R|/2, that is 2deg(x) is at most n-z-2.

The center contains 0, so z is at least 1, and one noncentral element gives n at least z+2. The neighbourhood-clique bound gives an energy at most twice the sum of max(deg(v)-1,0), and each summand is at most max(n-z-4,0)/2. Finally 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.commutingGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.ringCenter`
- Dependency: [D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound](NeighbourhoodCliqueBound.md)
