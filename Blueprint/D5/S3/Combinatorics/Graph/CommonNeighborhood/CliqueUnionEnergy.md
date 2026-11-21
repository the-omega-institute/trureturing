# Common-neighbourhood energy of a union of cliques

## Abstract

The common-neighbourhood energy of a disjoint union of cliques, its sharp complete-graph bound and the equality cases.

**Definition 1.1 (The disjoint union of cliques).**

$$\forall x \in V,\; \forall y \in V,\; \operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{cliqueUnion}\left(f\right), x, y\right) \Leftrightarrow \left(x \ne y \land f\left(x\right) = f\left(y\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.cliqueUnion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Acknowledgement.* Rajat Kanti Nath; Walaa N. T. Fasfous; Kinkar Chandra Das; Yilun Shang (2021). *Common Neighborhood Energy of Commuting Graphs of Finite Groups*. DOI: [10.3390/sym13091651](https://doi.org/10.3390/sym13091651). URL: <https://doi.org/10.3390/sym13091651>.

*Commentary.*

For a vertex type V and a labelling f from V to an arbitrary type, cliqueUnion(f) joins two distinct vertices exactly when they carry the same label. Its cliques are the fibres of f, and every disjoint union of complete graphs arises this way from the map sending a vertex to its component.

**Definition 1.2 (Clique orders).**

$$\forall i \in \iota,\; \operatorname{fibreCard}\left(f, i\right) = \operatorname{Finset}.\operatorname{card}\left(\{x:V\mid f\left(x\right) = i\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.fibreCard` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

fibreCard(f,i) is the number of vertices labelled i, so the clique orders s_i are the values of fibreCard(f,i) at the labels i in the image of f, and the number k of cliques is the cardinality of that image.

**Theorem 1.3 (Energy, bound and equality).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{cliqueUnion}\left(f\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) = 2 \cdot \sum_{i \in \operatorname{Finset}.\operatorname{image}\left(f, \operatorname{Finset}.\operatorname{univ}\right)} (((\operatorname{fibreCard}\left(f, i\right):\mathbb{R}) - 1) \cdot ((\operatorname{fibreCard}\left(f, i\right):\mathbb{R}) - 2)) \land \left(\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{cliqueUnion}\left(f\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) \le 2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(V\right):\mathbb{R}) - 1) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(V\right):\mathbb{R}) - 2) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{graphEnergy}\left(\operatorname{cliqueUnion}\left(f\right), \operatorname{D5}.\operatorname{S3}.\operatorname{Combinatorics}.\operatorname{Graph}.\operatorname{SubgroupGenerating}.\operatorname{CyclicExtensionRefutation}.\operatorname{MatrixKind}.\operatorname{commonNeighbour}\right) = 2 \cdot ((\operatorname{Fintype}.\operatorname{card}\left(V\right):\mathbb{R}) - 1) \cdot ((\operatorname{Fintype}.\operatorname{card}\left(V\right):\mathbb{R}) - 2) \Leftrightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{image}\left(f, \operatorname{Finset}.\operatorname{univ}\right)\right) = 1 \lor (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{image}\left(f, \operatorname{Finset}.\operatorname{univ}\right)\right) = 2 \land \left(\forall i \in i \in \operatorname{Finset}.\operatorname{image}\left(f, \operatorname{Finset}.\operatorname{univ}\right),\; \operatorname{fibreCard}\left(f, i\right) = 1\right))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Proofs of Nath–Fasfous–Das–Shang's commuting and surface conjectures, and a sharp form of Tak–Dutta–Nath's clique theorem*. DOI: [10.5281/zenodo.24398996](https://doi.org/10.5281/zenodo.24398996). URL: <https://doi.org/10.5281/zenodo.24398996>.

*Commentary.*

For every finite vertex type V with n vertices and every labelling f, the common-neighbourhood energy of cliqueUnion(f) equals twice the sum of (s_i-1)(s_i-2) over the cliques. It is at most the complete-graph value 2(n-1)(n-2), and equality holds exactly when there is one clique, or two cliques that are both single vertices. The energy is graphEnergy(g,commonNeighbour) of the noncentral commuting-graph module, the sum of the absolute values of the real eigenvalues of the common-neighbour matrix with multiplicity. The statement needs no hypothesis k at least one: with V empty the energy is 0, the bound 2(0-1)(0-2)=4 is strict, and the right side of the equality criterion is false. This is Proposition 7 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996. Theorem 5.4 of Tak, Dutta and Nath, arXiv:2605.22160v1, states the strict inequality, which fails exactly for a single clique and for two isolated vertices; only the non-strict bound is attributable to it.

Two distinct vertices of a clique of order s have s-2 common neighbours, and vertices of different cliques have none. Let Pi be the matrix with entry 1/s on pairs from one clique of order s and 0 otherwise. It is symmetric and idempotent, the orthogonal projection onto vectors constant on each clique. With the clique-constant weights W=(s-2)(s-1) and W'=max(s-2,0), the common-neighbour matrix equals P-Q for P=W Pi and Q=W'(1-Pi); the weight W' may replace s-2 because 1-Pi vanishes on cliques of order one. Both P and Q are positive semidefinite, as conjugates of nonnegative diagonal matrices by Pi and 1-Pi.

The energy of P-Q is at most tr P + tr Q by the positive-semidefinite difference bound of the noncentral commuting-graph module. For the reverse inequality put S=2 Pi-1. Then 1+S=2 Pi and 1-S=2(1-Pi) are positive semidefinite, so in an orthonormal eigenbasis of the common-neighbour matrix every diagonal entry of S lies in [-1,1], and tr(CS) is at most the sum of the absolute eigenvalues. Since P Pi=P and Q Pi=0, the product CS equals P+Q, so the energy is exactly tr P + tr Q. Each vertex of a clique of order s contributes 2(s-1)(s-2)/s, and summing over the s vertices of each clique gives the displayed formula.

For the bound write g(s)=(s-1)(s-2) and let D be g(n) minus the sum of g(s_i). Adding a clique of order a to cliques of total order N changes D by g(a+N)-g(a)-g(N)=2aN-2. Induction gives D=2 with no clique, D=0 with one clique, and D at least (k-1)(k-2)+2(n-k) with k at least two cliques. Hence D is nonnegative; D=0 forces k at most two, and with k=2 it forces n=2, so both cliques are single vertices; conversely two single vertices give D=g(2)=0.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.cliqueUnion`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.fibreCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.result`
- Dependency: [D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound](NoncentralBound.md)
