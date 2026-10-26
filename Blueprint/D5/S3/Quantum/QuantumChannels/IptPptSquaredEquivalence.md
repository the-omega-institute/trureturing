# Equivalence of PPT-squared and IPT-squared

## Abstract

The complex PPT-squared conjecture is equivalent to the IPT-squared conjectures over the complex and real fields. The reverse implications use a two-dimensional flag and preserve composition.

**Definition 1.1 (Amplification).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; \operatorname{MatrixMap}.\operatorname{kron}\left(Phi, \operatorname{LinearMap}.\operatorname{id}:\operatorname{MatrixMap}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), K\right)\right)\left(P\right) = \operatorname{fun} (a: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right)) \mapsto Phi\left((\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j: \operatorname{Fin}\left(n\right)) \mapsto P\left((i, a.2), (j, b.2)\right))\right)\left(a.1, b.1\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausChannel.kron` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

MatrixMap.kron supplies the amplification Phi tensor the identity on Fin r; kron_id_apply gives the displayed coordinate expression. The scalar K represents the Lean parameter 𝕜 with its RCLike instance. All indices use Fin; ordered pairs put the map's factor first. This is the coordinate encoding of Section 8, PDF p. 18.

**Theorem 1.2 (Coordinates of an identity amplification).**

$$\forall (\mathbb{k}: \operatorname{Type}), [\operatorname{RCLike}\left(\mathbb{k}\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{k}\right) \to_{l[\mathbb{k}]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{k}\right),\; \forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \mathbb{k}\right),\; \forall a \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right),\; \forall b \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right),\; \operatorname{MatrixMap}.\operatorname{kron}\left(Phi, (\operatorname{LinearMap}.\operatorname{id}: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), \mathbb{k}\right))\right)\left(P, a, b\right) = Phi\left((\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j: \operatorname{Fin}\left(n\right)) \mapsto P\left((i, a.2), (j, b.2)\right))\right)\left(a.1, b.1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.kron_id_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over every RCLike field 𝕜 and all finite input, output and ancillary dimensions, amplifying a linear matrix map Phi by the identity applies Phi to each matrix slice with the ancillary indices fixed.

**Definition 1.3 (Complete positivity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right) \Leftrightarrow (\forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(P\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{MatrixMap}.\operatorname{kron}\left(Phi, \operatorname{LinearMap}.\operatorname{id}:\operatorname{MatrixMap}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), K\right)\right)\left(P\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

MatrixMap.IsCompletelyPositive states that a map is completely positive when every amplification preserves positive semidefiniteness. Matrix.PosSemidef is the pinned matrix predicate. Quantification includes r = 0; that case contains only the empty matrix.

**Definition 1.4 (Separable cone).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{SEP}\left(K, m, r\right) = \{X:\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right), K\right) \mid \exists k \in \mathbb{N},\; \exists x \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(m\right) \to K\right),\; \exists y \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(r\right) \to K\right),\; X = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\operatorname{fun} (a: K) \mapsto \operatorname{fun} (b: K) \mapsto a * b), \operatorname{Matrix}.\operatorname{vecMulVec}\left(x\left(j\right), \operatorname{star}\left(x\left(j\right)\right)\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(y\left(j\right), \operatorname{star}\left(y\left(j\right)\right)\right)\right))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.SEP` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 6 defines the separable cone by finite sums of products of rank-one positive matrices. Nonnegative coefficients are absorbed into the vectors. The displayed finite sum runs over all j : Fin k. Matrix.kroneckerMap uses scalar multiplication of entries, and star acts pointwise on each vector.

**Definition 1.5 (Entanglement breaking).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsEB}\left(Phi\right) \Leftrightarrow (\forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(P\right)) \Rightarrow (\operatorname{MatrixMap}.\operatorname{kron}\left(Phi, \operatorname{LinearMap}.\operatorname{id}:\operatorname{MatrixMap}\left(\operatorname{Fin}\left(r\right), \operatorname{Fin}\left(r\right), K\right)\right)\left(P\right) \in \operatorname{SEP}\left(K, m, r\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsEB` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 8, PDF p. 18: "For p = 1, we just call the map Φ 𝕂-entanglement breaking." Its preceding condition is (Φ ⊗ idᵣ)(P) ∈ SEPₚ(𝕂ᵐ ⊗ 𝕂ʳ) for all positive P and r ≥ 1. The display specializes p to one and adds only the vacuous empty amplification. No trace-preserving or unital condition is imposed.

**Definition 1.6 (Input-first Choi matrix).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{Matrix}.\operatorname{submatrix}\left((\operatorname{fun} (j: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right) = \operatorname{fun} (a: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(a.1, b.1, 1\right)\right)\left(a.2, b.2\right)$$

*Formalization.* `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

MatrixMap.choi_matrix supplies the displayed output-first coordinate expression; submatrix Prod.swap Prod.swap puts the input factor first. Applying Phi to the matrix unit Matrix.single a.1 b.1 1 gives its entry at output indices a.2 and b.2. The canonical Kraus Choi matrix places output first; Prod.swap relates the two tensor orders.

**Theorem 1.7 (Complete positivity gives Choi positivity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{Matrix}.\operatorname{submatrix}\left((\operatorname{fun} (j: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.choi_psd_of_cp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every RCLike scalar field K and all natural dimensions n and m, a completely positive K-linear map Phi from n by n matrices to m by m matrices has a positive semidefinite input-first Choi matrix. The input-first matrix is MatrixMap.choi_matrix Phi with both indices composed with Prod.swap. The IPT-to-PPT implication uses this positivity, and swapping the tensor factors again gives the output-first positivity used for qubit channels.

**Definition 1.8 (Partial transpose on the first factor).**

$$\forall K \in \operatorname{Type},\; \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right), K\right),\; \operatorname{ptFirst}\left(X\right) = \operatorname{fun} (a: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto X\left((b.1, a.2), (a.1, b.2)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ptFirst` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

The first coordinates are exchanged and the second coordinates retained. This is τₙ tensor idₘ in Section 9.1, PDF p. 21; it is an ordinary transpose without complex conjugation.

**Definition 1.9 (PPT maps).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsPPT}\left(Phi\right) \Leftrightarrow ((\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{ptFirst}\left(\operatorname{Matrix}.\operatorname{submatrix}\left((\operatorname{fun} (j: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsPPT` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.1, PDF p. 21: "A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT)." Here PPT requires the first-factor partial transpose of the Choi matrix to be positive semidefinite.

**Definition 1.10 (IPT maps).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsIPT}\left(Phi\right) \Leftrightarrow ((\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right)) \land (\operatorname{ptFirst}\left(\operatorname{Matrix}.\operatorname{submatrix}\left((\operatorname{fun} (j: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right)\right) = \operatorname{Matrix}.\operatorname{submatrix}\left((\operatorname{fun} (j: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (k: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(j.2, k.2, 1\right)\right)\left(j.1, k.1\right)), \operatorname{Prod}.\operatorname{swap}, \operatorname{Prod}.\operatorname{swap}\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsIPT` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.1, PDF p. 21: "A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT)." Here IPT requires equality of the Choi matrix with its first-factor partial transpose.

**Definition 1.11 (The complex PPT-squared conjecture).**

$$PPT2C \Leftrightarrow (\forall n \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to_{l[\mathbb{C}]} \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{IsPPT}\left(Phi\right)) \Rightarrow (\operatorname{IsEB}\left((Phi \circ_{l} Phi)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.PPT2C` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Conjecture 9.5, PDF p. 23: "For every PPT map Φ : Mₙ(ℂ) → Mₙ(ℂ), Φ ◦ Φ is ℂ-entanglement breaking." The dimension n is universally quantified. The linear-map composition Phi ∘ₗ Phi is the square.

**Definition 1.12 (The IPT-squared conjecture).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \operatorname{IPT2}\left(K\right) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; (\operatorname{IsIPT}\left(Phi\right)) \Rightarrow (\operatorname{IsEB}\left((Phi \circ_{l} Phi)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IPT2` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Conjecture 9.7, PDF p. 24: "For 𝕂 ∈ {ℝ, ℂ}, every IPT map Φ : Mₙ(𝕂) → Mₙ(𝕂) satisfies Φ ◦ Φ is 𝕂-entanglement breaking." The definition is generic over RCLike K and is used at ℝ and ℂ. Zero dimension adds only a vacuous case.

**Definition 1.13 (The equivalence question).**

$$claim \Leftrightarrow ((PPT2C \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{C}\right))) \land (\operatorname{IPT2}\left(\mathbb{C}\right) \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{R}\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.claim` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.2, after Proposition 9.9, PDF p. 25: "We do not know if these conjectures are equivalent." The encoding is the conjunction (PPT2C ↔ IPT2 ℂ) ∧ (IPT2 ℂ ↔ IPT2 ℝ). Each conjecture ranges over all dimensions; this does not assert that the conjectures themselves are true.

**Remark 1.14 (A composition-compatible flag).**

$$
\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)), (\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)), \mathbb{C}\right),\; \forall Pplus \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall Pminus \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; ((Pplus = \frac{((1, \operatorname{Complex}.\operatorname{I}) ((1, \operatorname{Complex}.\operatorname{I}))^{*})}{2}) \land (Pminus = \frac{((1, -\operatorname{Complex}.\operatorname{I}) ((1, -\operatorname{Complex}.\operatorname{I}))^{*})}{2})) \Rightarrow (((\operatorname{Matrix}.\operatorname{PosSemidef}\left(rho\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(((rho)^{\Gamma_{\operatorname{B}}})\right))) \Rightarrow (\exists rhotilde \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \times \operatorname{Fin}\left(2\right)), ((\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (rhotilde = ((\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\operatorname{fun} (a: \mathbb{C}) \mapsto \operatorname{fun} (b: \mathbb{C}) \mapsto a * b), rho, Pplus\right)) + (\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\operatorname{fun} (a: \mathbb{C}) \mapsto \operatorname{fun} (b: \mathbb{C}) \mapsto a * b), ((rho)^{\Gamma_{\operatorname{B}}}), Pminus\right)))) \land ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(rhotilde\right)) \land ((rhotilde)^{\Gamma_{\operatorname{B}\operatorname{B}'}} = rhotilde))))
$$

*Citation.* Marcus Huber; Ludovico Lami; Cécilia Lancien; Alexander Müller-Hermes (2018). *High-Dimensional Entanglement in States with Positive Partial Transposition*. DOI: [10.1103/PhysRevLett.121.200503](https://doi.org/10.1103/PhysRevLett.121.200503). URL: <https://arxiv.org/abs/1802.04975>.

*Commentary.*

On the auxiliary two-dimensional factor take P+ = (1,i)(1,i)*/2 and P- = (1,-i)(1,-i)*/2. Their transpose exchanges them. Compress to these flag sectors with B+ and B-, and put E(X) = B+(X) + B-(X)^T and D(A) = A tensor P+ + A^T tensor P-. The lift D Phi E/2 has four completely positive branches for every complex PPT Phi. It is invariant under transpose on input and output, so its real restriction is IPT and complexifies back to the lift. The identity E D = 2 id makes the lift preserve composition. Completely positive insertion A tensor P+ and compression B+ recover Phi squared divided by two. This transfers entanglement breaking from the lifted square. The lift adapts the conjugate-flag construction rho tensor P+ + rho partially transposed tensor P- of Huber, Lami, Lancien and Müller-Hermes, arXiv v1, Section III.C, PDF p. 8, the second lemma labelled III.1. The map normalization, composition law and recovery are the consequences used here.

**Definition 1.15 (Normalized finite separable mixtures).**

$$\forall X \in \operatorname{Type},\; [\operatorname{Fintype}\left(X\right)] \forall Y \in \operatorname{Type},\; [\operatorname{Fintype}\left(Y\right)] \forall rho \in \operatorname{Matrix}\left(X \times Y, X \times Y, \mathbb{C}\right),\; \operatorname{IsSeparable}\left(rho\right) \Leftrightarrow (\exists n \in \mathbb{N},\; \exists p \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \exists sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(X, X, \mathbb{C}\right),\; \exists tau \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(Y, Y, \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 \le p\left(i\right)) \land ((\sum_{i:\operatorname{Fin}\left(n\right)} (p\left(i\right)) = 1) \land ((\forall i \in \operatorname{Fin}\left(n\right),\; ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(sigma\left(i\right)\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(sigma\left(i\right)\right) = 1)) \land ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(tau\left(i\right)\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(tau\left(i\right)\right) = 1))) \land (rho = \sum_{i:\operatorname{Fin}\left(n\right)} (\operatorname{HSMul}.\operatorname{hSMul}\left((p\left(i\right): \mathbb{C}), \operatorname{Matrix}.\operatorname{kronecker}\left(sigma\left(i\right), tau\left(i\right)\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsSeparable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A separable bipartite matrix is a finite convex mixture of tensor products of positive semidefinite trace-one matrices. The two index types are arbitrary finite types.

**Definition 1.16 (The conditional ancillary matrix).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; \operatorname{weighted}\left(M, P\right) = \operatorname{fun} (u: \operatorname{Fin}\left(r\right)) \mapsto \operatorname{fun} (v: \operatorname{Fin}\left(r\right)) \mapsto \operatorname{Matrix}.\operatorname{trace}\left((M*(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j: \operatorname{Fin}\left(n\right)) \mapsto P\left((i, u), (j, v)\right)))\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The effect M is paired by trace with each system slice of P; the remaining two coordinates index the ancillary matrix.

**Theorem 1.17 (Positive conditional ancillary matrices).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall M \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(M\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(P\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{weighted}\left(M, P\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive effect and a positive joint input give a positive conditional ancillary matrix, by rank-one decomposition and positive congruence.

**Definition 1.18 (Finite positive measure-and-prepare form).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{HasPrepare}\left(Phi\right) \Leftrightarrow (\exists k \in \mathbb{N},\; \exists M \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \exists N \in \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; (\forall j \in \operatorname{Fin}\left(k\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(M\left(j\right)\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(N\left(j\right)\right))) \land (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; Phi\left(A\right) = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{Matrix}.\operatorname{trace}\left((M\left(j\right) * A)\right) \cdot N\left(j\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.HasPrepare` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite family of positive measurement matrices M and positive preparation matrices N represents Phi by the sum of trace(M(j) A) times N(j), for every input matrix A. The natural number k counts all terms; n and m are arbitrary input and output dimensions over an RCLike scalar field K. Scalar multiplication is displayed by a centered dot.

**Theorem 1.19 (Positive measure-and-prepare maps break entanglement).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; (\operatorname{HasPrepare}\left(Phi\right)) \Rightarrow (\operatorname{IsEB}\left(Phi\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.prepare_eb` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive amplified input has separable output under a map with finite positive measure-and-prepare form. Positivity of each weighted matrix follows from a rank-one decomposition of the measurement matrix and positive congruence of the input; tensor products with the positive preparations then form a finite separable sum.

**Theorem 1.20 (Composition preserves complete positivity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(p\right), \operatorname{Fin}\left(p\right), K\right),\; \forall Psi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right)) \Rightarrow ((\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Psi\right)) \Rightarrow (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left((Phi) \circ_{l} (Psi)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.cp_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The composition of completely positive linear matrix maps is completely positive, over every RCLike field and all finite dimensions.

**Theorem 1.21 (Double transposition preserves complete positivity).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to_{l[\mathbb{C}]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}\right),\; (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left(Phi\right)) \Rightarrow (\operatorname{MatrixMap}.\operatorname{IsCompletelyPositive}\left((\operatorname{LinearEquiv}.\operatorname{toLinearMap}\left(\operatorname{Matrix}.\operatorname{transposeLinearEquiv}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{C}, \mathbb{C}\right)\right)) \circ_{l} ((Phi) \circ_{l} (\operatorname{LinearEquiv}.\operatorname{toLinearMap}\left(\operatorname{Matrix}.\operatorname{transposeLinearEquiv}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}, \mathbb{C}\right)\right)))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.cp_double_tau` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every completely positive complex-linear matrix map, transposing its input and output gives a completely positive map. Input and output dimensions may differ.

**Theorem 1.22 (The three conjectures are equivalent).**

$$(PPT2C \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{C}\right))) \land (\operatorname{IPT2}\left(\mathbb{C}\right) \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{R}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result` (`✓ std3`). ∎

*Resolves.* `Problems/chiribella-davidson-paulsen-rahaman-2023-ppt-ipt-squared-equivalence` (proved) by `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chiribella-davidson-paulsen-rahaman-2023-ppt-ipt-squared-equivalence","declaration_gid":"D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

IPT² over either field in dimension 2n implies PPT² over ℂ in dimension n by the flag lift and recovery. The source's implications PPT²(ℂ) ⇒ IPT²(ℂ) ⇒ IPT²(ℝ) retain dimension n. Entanglement breaking is characterized by a separable input-first Choi matrix, with an explicit tensor swap, and by measure-and-prepare form. Completely positive maps preserve it under pre- and post-composition. The complexification of a real entanglement-breaking map is complex entanglement breaking; in the reverse direction the IPT condition gives CSEP ∩ IPT = real SEP. These facts close both equivalences. The PPT-squared conjecture itself and the possibility of avoiding dimension doubling remain open.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.IsCompletelyPositive`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausChannel.kron`
- Truth anchor: `D5/S3/Quantum/Foundation/FiniteKrausRepresentation.choi_matrix`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.HasPrepare`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IPT2`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsEB`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsIPT`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsPPT`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsSeparable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.PPT2C`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.SEP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.choi_psd_of_cp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.cp_comp`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.cp_double_tau`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.kron_id_apply`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.prepare_eb`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ptFirst`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.weighted_psd`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](../../Weil/Probability/FiniteGaussianSchoenberg.md)
