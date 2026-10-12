# Equivalence of PPT-squared and IPT-squared

## Abstract

The complex PPT-squared conjecture is equivalent to the IPT-squared conjectures over the complex and real fields. The reverse implications use a two-dimensional flag and preserve composition.

**Definition 1.1 (Amplification).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; \operatorname{ampl}\left(Phi, r, P\right) = \operatorname{fun} (a: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right)) \mapsto Phi\left((\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j: \operatorname{Fin}\left(n\right)) \mapsto P\left((i, a.2), (j, b.2)\right))\right)\left(a.1, b.1\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ampl` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

The amplification is Phi tensor the identity on Fin r. The scalar K represents the Lean parameter 𝕜 with its RCLike instance. All indices use Fin; ordered pairs put the map's factor first. This is the coordinate encoding of Section 8, PDF p. 18.

**Definition 1.2 (Complete positivity).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsCP}\left(Phi\right) \Leftrightarrow (\forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(P\right)) \Rightarrow (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{ampl}\left(Phi, r, P\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsCP` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

A map is completely positive when every amplification preserves positive semidefiniteness. Matrix.PosSemidef is the pinned matrix predicate. Quantification includes r = 0; that case contains only the empty matrix.

**Definition 1.3 (Separable cone).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{SEP}\left(K, m, r\right) = \{X:\operatorname{Matrix}\left(\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(r\right), K\right) \mid \exists k \in \mathbb{N},\; \exists x \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(m\right) \to K\right),\; \exists y \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(r\right) \to K\right),\; X = \sum_{j:\operatorname{Fin}\left(k\right)} (\operatorname{Matrix}.\operatorname{kroneckerMap}\left((\operatorname{fun} (a: K) \mapsto \operatorname{fun} (b: K) \mapsto a * b), \operatorname{Matrix}.\operatorname{vecMulVec}\left(x\left(j\right), \operatorname{star}\left(x\left(j\right)\right)\right), \operatorname{Matrix}.\operatorname{vecMulVec}\left(y\left(j\right), \operatorname{star}\left(y\left(j\right)\right)\right)\right))\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.SEP` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 6 defines the separable cone by finite sums of products of rank-one positive matrices. Nonnegative coefficients are absorbed into the vectors. The displayed finite sum runs over all j : Fin k. Matrix.kroneckerMap uses scalar multiplication of entries, and star acts pointwise on each vector.

**Definition 1.4 (Entanglement breaking).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsEB}\left(Phi\right) \Leftrightarrow (\forall r \in \mathbb{N},\; \forall P \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(r\right), K\right),\; (\operatorname{Matrix}.\operatorname{PosSemidef}\left(P\right)) \Rightarrow (\operatorname{ampl}\left(Phi, r, P\right) \in \operatorname{SEP}\left(K, m, r\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsEB` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 8, PDF p. 18: "For p = 1, we just call the map Φ 𝕂-entanglement breaking." Its preceding condition is (Φ ⊗ idᵣ)(P) ∈ SEPₚ(𝕂ᵐ ⊗ 𝕂ʳ) for all positive P and r ≥ 1. The display specializes p to one and adds only the vacuous empty amplification. No trace-preserving or unital condition is imposed.

**Definition 1.5 (Input-first Choi matrix).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{choi}\left(Phi\right) = \operatorname{fun} (a: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto Phi\left(\operatorname{Matrix}.\operatorname{single}\left(a.1, b.1, 1\right)\right)\left(a.2, b.2\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.choi` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

The Choi matrix has its input factor first. Applying Phi to the matrix unit Matrix.single a.1 b.1 1 gives its entry at output indices a.2 and b.2. The canonical Kraus Choi matrix places output first; Prod.swap relates the two tensor orders.

**Definition 1.6 (Partial transpose on the first factor).**

$$\forall K \in \operatorname{Type},\; \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right), \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right), K\right),\; \operatorname{ptFirst}\left(X\right) = \operatorname{fun} (a: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto \operatorname{fun} (b: \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(m\right)) \mapsto X\left((b.1, a.2), (a.1, b.2)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ptFirst` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

The first coordinates are exchanged and the second coordinates retained. This is τₙ tensor idₘ in Section 9.1, PDF p. 21; it is an ordinary transpose without complex conjugation.

**Definition 1.7 (PPT maps).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsPPT}\left(Phi\right) \Leftrightarrow ((\operatorname{IsCP}\left(Phi\right)) \land (\operatorname{Matrix}.\operatorname{PosSemidef}\left(\operatorname{ptFirst}\left(\operatorname{choi}\left(Phi\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsPPT` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.1, PDF p. 21: "A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT)." Here PPT requires the first-factor partial transpose of the Choi matrix to be positive semidefinite.

**Definition 1.8 (IPT maps).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), K\right),\; \operatorname{IsIPT}\left(Phi\right) \Leftrightarrow ((\operatorname{IsCP}\left(Phi\right)) \land (\operatorname{ptFirst}\left(\operatorname{choi}\left(Phi\right)\right) = \operatorname{choi}\left(Phi\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsIPT` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.1, PDF p. 21: "A completely positive map Φ : Mₙ(𝕂) → Mₘ(𝕂) is called PPT (IPT) if its Choi matrix is PPT (IPT)." Here IPT requires equality of the Choi matrix with its first-factor partial transpose.

**Definition 1.9 (The complex PPT-squared conjecture).**

$$PPT2C \Leftrightarrow (\forall n \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right) \to_{l[\mathbb{C}]} \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{IsPPT}\left(Phi\right)) \Rightarrow (\operatorname{IsEB}\left((Phi \circ_{l} Phi)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.PPT2C` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Conjecture 9.5, PDF p. 23: "For every PPT map Φ : Mₙ(ℂ) → Mₙ(ℂ), Φ ◦ Φ is ℂ-entanglement breaking." The dimension n is universally quantified. The linear-map composition Phi ∘ₗ Phi is the square.

**Definition 1.10 (The IPT-squared conjecture).**

$$\forall K \in \operatorname{Type},\; [\operatorname{RCLike}\left(K\right)] \operatorname{IPT2}\left(K\right) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall Phi \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right) \to_{l[K]} \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; (\operatorname{IsIPT}\left(Phi\right)) \Rightarrow (\operatorname{IsEB}\left((Phi \circ_{l} Phi)\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IPT2` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Conjecture 9.7, PDF p. 24: "For 𝕂 ∈ {ℝ, ℂ}, every IPT map Φ : Mₙ(𝕂) → Mₙ(𝕂) satisfies Φ ◦ Φ is 𝕂-entanglement breaking." The definition is generic over RCLike K and is used at ℝ and ℂ. Zero dimension adds only a vacuous case.

**Definition 1.11 (The equivalence question).**

$$claim \Leftrightarrow ((PPT2C \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{C}\right))) \land (\operatorname{IPT2}\left(\mathbb{C}\right) \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{R}\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.claim` (`✓ std3`).

*Citation.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

Section 9.2, after Proposition 9.9, PDF p. 25: "We do not know if these conjectures are equivalent." The encoding is the conjunction (PPT2C ↔ IPT2 ℂ) ∧ (IPT2 ℂ ↔ IPT2 ℝ). Each conjecture ranges over all dimensions; this does not assert that the conjectures themselves are true.

**Remark 1.12 (A composition-compatible flag).**

$$
(PPT2C \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{C}\right))) \land (\operatorname{IPT2}\left(\mathbb{C}\right) \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{R}\right)))
$$

*Citation.* Marcus Huber; Ludovico Lami; Cécilia Lancien; Alexander Müller-Hermes (2018). *High-Dimensional Entanglement in States with Positive Partial Transposition*. DOI: [10.1103/PhysRevLett.121.200503](https://doi.org/10.1103/PhysRevLett.121.200503). URL: <https://arxiv.org/abs/1802.04975>.

*Commentary.*

On the auxiliary two-dimensional factor take P+ = (1,i)(1,i)*/2 and P- = (1,-i)(1,-i)*/2. Their transpose exchanges them. Compress to these flag sectors with B+ and B-, and put E(X) = B+(X) + B-(X)^T and D(A) = A tensor P+ + A^T tensor P-. The lift D Phi E/2 has four completely positive branches for every complex PPT Phi. It is invariant under transpose on input and output, so its real restriction is IPT and complexifies back to the lift. The identity E D = 2 id makes the lift preserve composition. Completely positive insertion A tensor P+ and compression B+ recover Phi squared divided by two. This transfers entanglement breaking from the lifted square. The lift adapts the conjugate-flag construction rho tensor P+ + rho partially transposed tensor P- of Huber, Lami, Lancien and Müller-Hermes, arXiv v1, Section III.C, PDF p. 8, the second lemma labelled III.1. The map normalization, composition law and recovery are the consequences used here.

**Theorem 1.13 (The three conjectures are equivalent).**

$$(PPT2C \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{C}\right))) \land (\operatorname{IPT2}\left(\mathbb{C}\right) \Leftrightarrow (\operatorname{IPT2}\left(\mathbb{R}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Kenneth R. Davidson; Vern I. Paulsen; Mizanur Rahaman (2023). *Positive maps and entanglement in real Hilbert spaces*. DOI: [10.1007/s00023-023-01325-x](https://doi.org/10.1007/s00023-023-01325-x). URL: <https://arxiv.org/abs/2207.02510v2>.

*Commentary.*

IPT² over either field in dimension 2n implies PPT² over ℂ in dimension n by the flag lift and recovery. The source's implications PPT²(ℂ) ⇒ IPT²(ℂ) ⇒ IPT²(ℝ) retain dimension n. Entanglement breaking is characterized by a separable input-first Choi matrix, with an explicit tensor swap, and by measure-and-prepare form. Completely positive maps preserve it under pre- and post-composition. The complexification of a real entanglement-breaking map is complex entanglement breaking; in the reverse direction the IPT condition gives CSEP ∩ IPT = real SEP. These facts close both equivalences. The PPT-squared conjecture itself and the possibility of avoiding dimension doubling remain open.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IPT2`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsCP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsEB`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsIPT`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.IsPPT`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.PPT2C`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.SEP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ampl`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.choi`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.ptFirst`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Weil/Probability/FiniteGaussianSchoenberg](../../Weil/Probability/FiniteGaussianSchoenberg.md)
