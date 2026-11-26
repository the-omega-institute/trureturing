# The real degree matrix on connected threshold graphs

## Abstract

The degree-matrix specialization of the master-identity criterion

**Definition 1.1 (Threshold graphs).**

$$\forall V \in Type*,\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{IsThreshold}\left(G\right) \Leftrightarrow (\exists n \in \mathbb{N},\; \exists c \in \operatorname{Creation}\left(n\right),\; \operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, \operatorname{Creation}.\operatorname{graph}\left(c\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.IsThreshold` (`✓ std3`).

*Citation.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Threshold Graphs: A Survey*. URL: <https://arxiv.org/pdf/2610.22838v1#page=18>.

*Commentary.*

Section 1 of arXiv:2610.22838v1 starts from a singleton and allows isolated or dominating vertex additions. The internal type Creation(n) encodes exactly n additions. Creation.graph realizes the last addition at label zero, shifting old labels by one. The isomorphism allows any vertex labeling. Type* permits an arbitrary universe level.

**Definition 1.2 (Real eigenvalue multiset of the degree matrix).**

$$\forall V \in Type*,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{degreeSpectrum}\left(G\right) = \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{SimpleGraph}.\operatorname{degMatrix}\left(\mathbb{R}, G\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.degreeSpectrum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Threshold Graphs: A Survey*. URL: <https://arxiv.org/pdf/2610.22838v1#page=18>.

*Commentary.*

The matrix is the ordinary degree diagonal over the reals. Its characteristic polynomial has one linear factor per vertex, so the root multiset carries algebraic multiplicities, including repeated degrees.

**Definition 1.3 (The all-ones matrix).**

$$\forall V \in Type*,\; \forall i \in V,\; \forall j \in V,\; \operatorname{allOnes}\left(V, i, j\right) = 1 : \mathbb{R}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.allOnes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Threshold Graphs: A Survey*. URL: <https://arxiv.org/pdf/2610.22838v1#page=18>.

*Commentary.*

Every entry is the real number one. This is the matrix J in the conjecture.

**Definition 1.4 (The criterion specialized to the degree matrix).**

$$\operatorname{claim} \Leftrightarrow (((\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\forall x \in \mathbb{R},\; x \in \operatorname{degreeSpectrum}\left(G\right) \Rightarrow \left(\exists z \in \mathbb{Z},\; x = (z : \mathbb{R})\right)\right)\right)) \land (\forall V \in Type,\; \forall W \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(W\right)], [\operatorname{DecidableEq}\left(W\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(H\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\operatorname{IsThreshold}\left(H\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(H\right) \Rightarrow \left(\operatorname{degreeSpectrum}\left(G\right) = \operatorname{degreeSpectrum}\left(H\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, H\right)\right)\right)\right)\right)\right))) \Leftrightarrow (\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\exists alpha \in \mathbb{R},\; \exists beta \in \mathbb{R},\; \exists gamma \in \mathbb{R},\; \operatorname{SimpleGraph}.\operatorname{degMatrix}\left(\mathbb{R}, G\right) = alpha \cdot \operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(\mathbb{R}, G\right) + beta \cdot \operatorname{allOnes}\left(V\right) + gamma \cdot (1 : \operatorname{Matrix}\left(V, V, \mathbb{R}\right))\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.claim` (`✓ std3`).

*Citation.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Threshold Graphs: A Survey*. URL: <https://arxiv.org/pdf/2610.22838v1#page=18>.

*Commentary.*

Conjecture 13.9 (printed p. 18) puts unconditional integrality and spectral determination together on the left. Section 2 supplies connectedness and the ordinary Laplacian. The two graphs in the determination clause may have different finite vertex types. The affine clause permits the real coefficients to depend on the graph. The matrix numeral one denotes the identity matrix.

**Theorem 1.5 (Failure of the degree-matrix criterion).**

$$\neg (((\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\forall x \in \mathbb{R},\; x \in \operatorname{degreeSpectrum}\left(G\right) \Rightarrow \left(\exists z \in \mathbb{Z},\; x = (z : \mathbb{R})\right)\right)\right)) \land (\forall V \in Type,\; \forall W \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(W\right)], [\operatorname{DecidableEq}\left(W\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(H\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\operatorname{IsThreshold}\left(H\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(H\right) \Rightarrow \left(\operatorname{degreeSpectrum}\left(G\right) = \operatorname{degreeSpectrum}\left(H\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, H\right)\right)\right)\right)\right)\right))) \Leftrightarrow (\forall V \in Type,\; [\operatorname{Fintype}\left(V\right)], [\operatorname{DecidableEq}\left(V\right)], \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)], \operatorname{IsThreshold}\left(G\right) \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(\exists alpha \in \mathbb{R},\; \exists beta \in \mathbb{R},\; \exists gamma \in \mathbb{R},\; \operatorname{SimpleGraph}.\operatorname{degMatrix}\left(\mathbb{R}, G\right) = alpha \cdot \operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(\mathbb{R}, G\right) + beta \cdot \operatorname{allOnes}\left(V\right) + gamma \cdot (1 : \operatorname{Matrix}\left(V, V, \mathbb{R}\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.not_degreeMatrix_master_identity_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pallabi Manna; Santanu Mandal; Fernando C. Tura (2026). *The Spectral Theory of Threshold Graphs: A Survey*. URL: <https://arxiv.org/pdf/2610.22838v1#page=18>.

*Commentary.*

The degrees are integral, and the root multiset recovers the degree multiset. In a threshold creation sequence, a zero degree identifies an isolated last addition. Cancel the last vertex and undo the old-degree shift after a dominating addition to recover the sequence. This reconstruction is classical, due to Chvátal and Hammer (1977). On the connected three-vertex path, the leaf nonedge forces beta to vanish and a center-to-leaf edge forces alpha to vanish. The center and leaf diagonal entries then force incompatible values of gamma.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.IsThreshold`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.allOnes`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.degreeSpectrum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/MannaMandalTuraDegreeMatrixRefutation.not_degreeMatrix_master_identity_criterion`
