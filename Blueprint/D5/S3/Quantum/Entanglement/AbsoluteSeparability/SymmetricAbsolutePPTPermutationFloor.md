# A partial-transpose floor for symmetric tensors

## Abstract

Permutation symmetrizers retain a positive floor under every site partial transpose.

**Definition 1.1 (Permutation invariant vectors).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall v \in \left(I \to L\right) \to \mathbb{C},\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(v\right)) \Leftrightarrow (\forall sigma \in \operatorname{Equiv.Perm}\left(I\right),\; \forall x \in I \to L,\; v\left(\operatorname{Function.comp}\left(x, sigma\right)\right) = v\left(x\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector` (`✓ std3`).

*Citation.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The source states on p. 1: “They satisfy ρ = πρπ′ with π and π′ any pair of permutation operators.” A symmetric vector is fixed by every site permutation; the site and local-label sets here are arbitrary finite types.

**Definition 1.2 (Permutation matrices on words).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(L\right)] \forall sigma \in \operatorname{Equiv.Perm}\left(I\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Q}\left(sigma\right) = \operatorname{Equiv.Perm.permMatrix}\left(\mathbb{C}, \operatorname{Equiv.arrowCongr}\left(\operatorname{Equiv.symm}\left(sigma\right), \operatorname{Equiv.refl}\left(L\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The inverse site permutation reindexes functions. The associated permutation matrix sends v to the vector x mapped to v(x composed with sigma).

**Definition 1.3 (Permutation symmetrizer).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right) = \operatorname{Finset.expect}\left(\operatorname{Finset.univ}, \operatorname{fun} (sigma: \operatorname{Equiv.Perm}\left(I\right)) \mapsto \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Q}\left(sigma\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Averaging the word permutation matrices gives the orthogonal projector onto symmetric vectors.

**Definition 1.4 (Local symmetric projector).**

$$\forall I \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall L \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) = \operatorname{Finset.expect}\left(\operatorname{Finset.univ}, \operatorname{fun} (g: \operatorname{MulAction.stabilizer}\left(\operatorname{Equiv.Perm}\left(I\right), S\right)) \mapsto \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Q}\left(\operatorname{Subtype.val}\left(g\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.localP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The stabilizer of a site subset permutes that subset and its complement independently. Its average is the projector onto the tensor product of their symmetric subspaces.

**Theorem 1.5 (Hermitian symmetrizer).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Inversion permutes the summands of the adjoint average.

**Theorem 1.6 (Idempotent symmetrizer).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right) \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right) = \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Multiplying a finite group average by itself preserves it.

**Theorem 1.7 (Symmetric image).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall v \in \left(I \to L\right) \to \mathbb{C},\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The averaged vector is invariant under every site permutation.

**Theorem 1.8 (Fixed symmetric vectors).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall v \in \left(I \to L\right) \to \mathbb{C},\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector}\left(v\right)) \Rightarrow (\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right), v\right) = v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

Every site permutation fixes a symmetric vector, so their average does as well.

**Theorem 1.9 (Hermitian local projector).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The stabilizer average is Hermitian.

**Theorem 1.10 (Idempotent local projector).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) = \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The stabilizer average is idempotent.

**Theorem 1.11 (Positive local projector).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

A Hermitian idempotent matrix is positive semidefinite.

**Theorem 1.12 (Local support of the symmetrizer).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right) = \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_mul_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

A fully symmetric vector is symmetric on either side of any site partition.

**Theorem 1.13 (Partial transpose of a local sandwich).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \forall Y \in \operatorname{Matrix}\left(I \to L, I \to L, \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) \cdot Y \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right)\right) = \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right) \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, Y\right) \cdot \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The two local projectors are real symmetric. Their tensor product can pass through partial transposition on either side of a matrix.

**Theorem 1.14 (Positive floor after partial transpose).**

$$\forall I \in \operatorname{Type},\; \forall L \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)] \forall S \in \operatorname{Finset}\left(I\right),\; \operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound.partialTransposeOn}\left(S, \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.P}\left(I, L\right)\right) - (((\operatorname{Nat.choose}\left(\operatorname{Fintype.card}\left(I\right), \operatorname{Finset.card}\left(S\right)\right): \mathbb{C}))^{-1}) \cdot (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor.Local.localP}\left(S\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* J. Louvet, E. Serrano-Ensástiga, T. Bastin, J. Martin (2025). *Nonequivalence between absolute separability and positive partial transposition in the symmetric subspace*. DOI: [10.1103/PhysRevA.111.042418](https://doi.org/10.1103/PhysRevA.111.042418). URL: <https://arxiv.org/abs/2411.16461v2>.

*Commentary.*

The cosets of the subset stabilizer have representatives that exchange equally many sites across the partition. Each partially transposed representative is a Gram matrix. The identity representative supplies the displayed floor; all other contributions are positive.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.IsSymmetricVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_idempotent`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_mulVec_of_symmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.P_mulVec_symmetric`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_hermitian`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_idempotent`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_mul_P`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.PiS_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.Q`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.localP`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.partialTranspose_PiS_sandwich`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPermutationFloor.symmetrizer_partialTranspose_floor`
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound](SymmetricAbsolutePPTPureBound.md)
