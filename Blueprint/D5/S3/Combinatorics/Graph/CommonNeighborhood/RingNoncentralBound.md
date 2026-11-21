# Common-neighbourhood energy of the noncentral commuting graph of a ring

## Abstract

The strict common-neighbourhood energy bound for the commuting graph of every finite noncommutative ring.

**Definition 1.1 (The center).**

$$\operatorname{ringCenter}\left(R\right) = \{x\mid \forall y \in R,\; x \cdot y = y \cdot x\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.ringCenter` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

ringCenter(R) is the centralizer of the whole ring, the set of elements commuting with every element of R. For an associative ring this is the usual center; in general it is the commutative center.

**Definition 1.2 (Individual noncentral vertices).**

$$\operatorname{Vertex}\left(R\right) = \{x:R\mid \neg x \in \operatorname{ringCenter}\left(R\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.Vertex` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

Vertex(R) is the subtype of elements outside the center; vertices are individual elements.

**Definition 1.3 (The commuting graph).**

$$\forall x \in \operatorname{Vertex}\left(R\right),\; \forall y \in \operatorname{Vertex}\left(R\right),\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{commutingGraph}\left(R\right), x, y\right) \Leftrightarrow \left(x \ne y \land x \cdot y = y \cdot x\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.commutingGraph` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

Two distinct noncentral elements are adjacent exactly when their two products in R are equal.

**Definition 1.4 (Centralizer orders).**

$$\forall x \in R,\; \operatorname{centralizerCard}\left(R, x\right) = \operatorname{Fintype}.\operatorname{card}\left(\{y:R\mid x \cdot y = y \cdot x\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.centralizerCard` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

centralizerCard(R,x) is the number of elements commuting with x.

**Theorem 1.5 (The strict bound).**

$$\forall R \in \operatorname{Type},\; [\operatorname{NonUnitalNonAssocRing}\left(R\right)][\operatorname{Fintype}\left(R\right)]\left(\exists a \in R,\; \exists b \in R,\; a \cdot b \ne b \cdot a\right) \Rightarrow \left(\left(1 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) \land \left(3 \cdot \operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right) \land \left(\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) + 2 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right) \land \left(3 \le \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right) \land \operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right) \mid \operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right)\right)\right)\right)\right) \land \left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{commutingGraph}\left(R\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le 2 \cdot \sum_{x: \operatorname{Vertex}\left(R\right)} \operatorname{max}\left((\operatorname{centralizerCard}\left(R, \operatorname{Subtype}.\operatorname{val}\left(x\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2, 0\right) \land \left(2 \cdot \sum_{x: \operatorname{Vertex}\left(R\right)} \operatorname{max}\left((\operatorname{centralizerCard}\left(R, \operatorname{Subtype}.\operatorname{val}\left(x\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2, 0\right) \le (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left(\frac{2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) + (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}))}{(\operatorname{Nat}.\operatorname{minFac}\left(\operatorname{Fintype}.\operatorname{card}\left(R\right)\right):\mathbb{R})} - 2 \cdot (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \land \left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left(\frac{2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) + (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}))}{(\operatorname{Nat}.\operatorname{minFac}\left(\operatorname{Fintype}.\operatorname{card}\left(R\right)\right):\mathbb{R})} - 2 \cdot (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \le (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \land \left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot \operatorname{max}\left((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 4, 0\right) \le (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2) \land (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{ringCenter}\left(R\right)\right):\mathbb{R}) - 2) < 2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - 1) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(R\right)\right):\mathbb{R}) - 2)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

Let R be a finite ring whose multiplication distributes over addition, associative or not and not necessarily unital, with two elements whose products differ. Write z for the order of its center, n for the number of noncentral elements, C(x) for the centralizer of x and p for the least prime dividing |R|. Then z is at least 1, n is at least 3z, n is at least z+2 and at least 3, and z divides n. The common-neighbourhood energy of commutingGraph(R) is at most twice the sum over noncentral x of max(|C(x)|-z-2,0); that sum is at most n max(2(n+z)/p-2z-4,0), which is at most n max(n-z-4,0), which is at most n(n-z-2), which is strictly below the complete-graph value 2(n-1)(n-2). For associative rings, n at least z+2 and the bound n(n-z-2) < 2(n-1)(n-2) are Corollary 3, and the per-vertex sum and the least-prime-divisor form are Corollary 4, of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996; the repository drops associativity and adds n at least 3z and z dividing n.

For a noncentral x, the elements commuting with x form an additive subgroup, because multiplication distributes over addition and negation. It is exactly the disjoint union of the center, x itself and the graph neighbours of x, so deg(x) = |C(x)|-z-1. It is proper since x is noncentral, so its index is a divisor of |R| exceeding one, hence at least p, and p|C(x)| is at most |R| = n+z. The center is itself an additive subgroup, properly contained in C(x) because x lies in C(x); by Lagrange |C(x)| is at least 2z and |R| at least 4z, so n is at least 3z, and z divides |R| and hence n.

The neighbourhood-clique bound gives an energy at most twice the sum of max(deg(x)-1,0), which is the displayed per-vertex sum. Each summand is at most max((n+z)/p-z-2,0), and p is at least 2. Finally 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive.

The hypotheses are needed as follows. Without two non-commuting elements the vertex type is empty and n is at least z+2 fails. Finiteness is needed for the orders and the spectrum. Additive inverses are needed for the centralizer to be an additive subgroup to which Lagrange's theorem applies; in a semiring the centralizer is only an additive submonoid. That last remark is not separately formalized. The four-element ring with a^2=a, ab=b, ba=0, b^2=0 has z=1, n=3 and no edges, so the energy equals the bound n max(n-z-4,0)=0; this example is not compiled.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.Vertex`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.centralizerCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.commutingGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.ringCenter`
- Dependency: [D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound](NeighbourhoodCliqueBound.md)
