# Half-trace bounds for partial transposition

## Abstract

Finite bipartite partial transposes satisfy a universal half-trace lower bound.

**Definition 1.1 (Partial transpose on tensor sites).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(I\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \forall rho \in \operatorname{Matrix}\left(I \to L, I \to L, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, rho\right) = \operatorname{fun} (x: I \to L) \mapsto \operatorname{fun} (y: I \to L) \mapsto rho\left(\operatorname{Finset.piecewise}\left(S, y, x\right), \operatorname{Finset.piecewise}\left(S, x, y\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.partialTransposeOn` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The entries on a chosen subset of sites are exchanged between the row and column labels.

**Theorem 1.2 (Partial transpose of finite sums).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(I\right)] \forall J \in \operatorname{Type},\; \forall S \in \operatorname{Finset}\left(I\right),\; \forall F \in J \to \operatorname{Matrix}\left(I \to L, I \to L, \mathbb{C}\right),\; \forall s \in \operatorname{Finset}\left(J\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, \operatorname{Finset.sum}\left(s, F\right)\right) = \operatorname{Finset.sum}\left(s, \operatorname{fun} (i: J) \mapsto \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, F\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.partialTranspose_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Partial transposition distributes over finite matrix sums.

**Theorem 1.3 (Antisymmetric product estimate).**

$$\forall A \in \operatorname{Type},\; \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{Fintype}\left(B\right)] \forall V \in \operatorname{Matrix}\left(A, B, \mathbb{C}\right),\; \forall M \in \operatorname{Matrix}\left(A, B, \mathbb{C}\right),\; \sum_{(i: B)} (\sum_{(j: B)} (\operatorname{Complex.normSq}\left(\left(\operatorname{Matrix.transpose}\left(V\right) \cdot M\right)\left(i, j\right) - \left(\operatorname{Matrix.transpose}\left(V\right) \cdot M\right)\left(j, i\right)\right))) \le 2 \cdot (\sum_{(i: A)} (\sum_{(j: B)} (\operatorname{Complex.normSq}\left(V\left(i, j\right)\right)))) \cdot (\sum_{(i: A)} (\sum_{(j: B)} (\operatorname{Complex.normSq}\left(M\left(i, j\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.antisymmetric_product_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The squared Frobenius mass of the antisymmetric part of a product is at most twice the product of the two squared Frobenius masses. Expanding row wedges and applying Cauchy–Schwarz gives this estimate.

**Theorem 1.4 (Compression of a lower bound).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall A \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \forall Q \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; \forall a \in \mathbb{R},\; (\operatorname{Matrix.IsHermitian}\left(Q\right)) \Rightarrow ((Q \cdot Q = Q) \Rightarrow ((Q \cdot A \cdot Q = A) \Rightarrow ((\operatorname{Matrix.PosSemidef}\left(A + (a) \cdot ((1: \operatorname{Matrix}\left(I, I, \mathbb{C}\right)))\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(A + (a) \cdot (Q)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.compress_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

A lower bound by a scalar identity compresses to the same scalar times any Hermitian projector supporting the matrix.

**Theorem 1.5 (Half-trace bound).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \forall A \in \operatorname{Matrix}\left(I \to L, I \to L, \mathbb{C}\right),\; (\operatorname{Matrix.PosSemidef}\left(A\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, A\right) + (\frac{\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(A\right)\right)}{2}) \cdot ((1: \operatorname{Matrix}\left(I \to L, I \to L, \mathbb{C}\right)))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The partial transpose of a positive matrix is bounded below by minus half its trace. The spectral decomposition reduces this inequality to unit rank-one matrices.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.antisymmetric_product_bound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.compress_lower`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.partialTransposeOn`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.partialTranspose_sum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.psd_partialTranspose_half_trace`
- Dependency: [D5/S3/Quantum/Recovery/PetzSpectralCoordinates](../../Recovery/PetzSpectralCoordinates.md)
