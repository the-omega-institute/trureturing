# The minimum overlap of orthogonal channel inputs

## Abstract

Orthogonal pure inputs to a classical–quantum channel have average output overlap at least the minimum over distinct basis inputs.

Matrices have complex entries. Fin n indexes the source's n computational basis vectors from zero; sigma is the family of output states, and u lists the input vectors. Products and traces are matrix products and Matrix.trace. Complex.re gives the real comparison. The sums over r and s count ordered pairs, with zero diagonal terms.

**Definition 1.1 (Quantum states).**

$$\forall d \in \mathbb{N},\; \forall sigma \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \operatorname{IsState}\left(sigma\right) \Leftrightarrow ((\operatorname{Matrix.PosSemidef}\left(sigma\right)) \land (\operatorname{Matrix.trace}\left(sigma\right) = 1))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.IsState` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

A quantum state in M_d(ℂ) is a positive semidefinite matrix with trace one.

**Definition 1.2 (Output on a pure input).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall u \in \operatorname{Fin}\left(n\right) \to \mathbb{C},\; \operatorname{channelOutput}\left(sigma, u\right) = \sum_{(i:\operatorname{Fin}\left(n\right))} (\operatorname{HSMul.hSMul}\left(\operatorname{Complex.ofReal}\left(\operatorname{Complex.normSq}\left(u\left(i\right)\right)\right), sigma\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.channelOutput` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

Definition 1.3, page 2: “A C–Q channel Φ from an n-qubit space to an m-qubit space is specified by 2ⁿ states σ₁, …, σ_{2ⁿ} on m qubits and acts as Φ(ρ) = Σᵢ Tr(|i⟩⟨i| ρ) σᵢ.” On a pure input, the coefficient is the squared modulus of its i-th coordinate. The formula below permits every finite input and output dimension.

**Definition 1.3 (Orthonormal input families).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall u \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right),\; \operatorname{IsOrthonormalFamily}\left(u\right) \Leftrightarrow (\forall r \in \operatorname{Fin}\left(k\right),\; \forall s \in \operatorname{Fin}\left(k\right),\; \sum_{(i:\operatorname{Fin}\left(n\right))} ((\operatorname{star}\left(u\left(r, i\right)\right)) \cdot (u\left(s, i\right))) = \operatorname{ite}\left(r = s, 1, 0\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.IsOrthonormalFamily` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

The vectors u₁, …, u_k are pairwise orthogonal pure states, or unit vectors, in ℂⁿ. Their coordinate inner products are one on the diagonal and zero off the diagonal.

**Definition 1.4 (Average output overlap).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall u \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right),\; \operatorname{averageOutputOverlap}\left(sigma, u\right) = (\frac{1}{((k:\mathbb{R})) \cdot ((k:\mathbb{R}) - 1)}) \cdot (\sum_{(r:\operatorname{Fin}\left(k\right))} (\sum_{(s:\operatorname{Fin}\left(k\right))} (\operatorname{ite}\left(r = s, 0, \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{channelOutput}\left(sigma, u\left(r\right)\right)) \cdot (\operatorname{channelOutput}\left(sigma, u\left(s\right)\right))\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.averageOutputOverlap` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

The left side of Conjecture 1.5, page 3, divides the sum over ordered unequal pairs by k(k−1). The displayed reciprocal and products are in the real numbers. The definition exists for every k; the theorem assumes k is at least two.

**Definition 1.5 (Minimum over distinct basis inputs).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall k \in \mathbb{N},\; \operatorname{minDistinctOverlap}\left(sigma, k\right) = \operatorname{iInf}_{(iota:\{ j:\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(n\right) // \operatorname{Function.Injective}\left(j\right) \})} ((\frac{1}{((k:\mathbb{R})) \cdot ((k:\mathbb{R}) - 1)}) \cdot (\sum_{(r:\operatorname{Fin}\left(k\right))} (\sum_{(s:\operatorname{Fin}\left(k\right))} (\operatorname{ite}\left(r = s, 0, \operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((sigma\left(\operatorname{Subtype.val}\left(iota\right)\left(r\right)\right)) \cdot (sigma\left(\operatorname{Subtype.val}\left(iota\right)\left(s\right)\right))\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.minDistinctOverlap` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

The right side of Conjecture 1.5, page 3, minimizes over k distinct basis indices. An injective map from Fin k to Fin n specifies the ordered list. Since the set of such maps is finite and is nonempty when k ≤ n, its real infimum is its minimum. Subtype.val extracts this injective map.

**Definition 1.6 (Conjecture 1.5).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsState}\left(sigma\left(i\right)\right)) \Rightarrow ((2 \le k) \Rightarrow ((k \le n) \Rightarrow (\forall u \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right),\; (\operatorname{IsOrthonormalFamily}\left(u\right)) \Rightarrow (\operatorname{minDistinctOverlap}\left(sigma, k\right) \le \operatorname{averageOutputOverlap}\left(sigma, u\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.claim` (`✓ std3`).

*Citation.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

Conjecture 1.5, page 3: “Let σ₁, …, σₙ ∈ M_d(ℂ) be arbitrary quantum states. Then for any collection of k ≤ n of pairwise orthogonal pure states |u₁⟩, …, |u_k⟩ ∈ ℂⁿ, the following bound holds: (1/(k(k−1))) Σ_{r≠s} Tr((Σᵢ |⟨i|u_r⟩|² σᵢ)(Σⱼ |⟨j|u_s⟩|² σⱼ)) ≥ min_{i₁,…,i_k ∈ [n] distinct} (1/(k(k−1))) Σ_{r≠s} Tr(σ_{i_r} σ_{i_s}).” A quantum state is positive semidefinite with trace one. The coordinate inner-product equality expresses that the pure input vectors have norm one and are pairwise orthogonal. The real reciprocal requires 2 ≤ k.

**Theorem 1.7 (The orthogonal lower bound).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall sigma \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsState}\left(sigma\left(i\right)\right)) \Rightarrow ((2 \le k) \Rightarrow ((k \le n) \Rightarrow (\forall u \in \operatorname{Fin}\left(k\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{C}\right),\; (\operatorname{IsOrthonormalFamily}\left(u\right)) \Rightarrow (\operatorname{minDistinctOverlap}\left(sigma, k\right) \le \operatorname{averageOutputOverlap}\left(sigma, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result` (`✓ std3`). ∎

*Resolves.* `Problems/hutton-mehta-vukovic-2025-cq-output-overlap-minimum` (proved) by `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hutton-mehta-vukovic-2025-cq-output-overlap-minimum","declaration_gid":"D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kiera Hutton; Arthur Mehta; Andrej Vukovic (2025). *Deciding whether a C–Q channel preserves a bit is QCMA-complete*. DOI: [10.48550/arXiv.2508.10664](https://doi.org/10.48550/arXiv.2508.10664). URL: <https://arxiv.org/abs/2508.10664v1>.

*Commentary.*

The squared absolute determinants of the k-row minors of the input matrix form a probability distribution on k-element subsets, by Cauchy–Binet and orthonormality. Its average subset overlap is at least the minimum subset overlap. The difference between the total output overlap and this average is a sum of traces of products TᴴT, where T is the cross combination Σᵢ conj(Uᵢᵣ)Uᵢₛσᵢ. Each term is nonnegative. Dividing by the positive real number k(k−1) gives the inequality. The residual identity uses Hermiticity; no non-orthogonal correction is asserted.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.IsOrthonormalFamily`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.IsState`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.averageOutputOverlap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.channelOutput`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.minDistinctOverlap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/HuttonMehtaVukovicOutputOverlap.result`
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
- Dependency: [D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation](../../QuantumChannels/CoPRelativeQuantumnessRefutation.md)
