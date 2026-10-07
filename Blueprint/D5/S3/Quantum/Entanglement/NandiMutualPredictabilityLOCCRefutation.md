# A local measure-and-reset refutes the LOCC monotonicity of I2

## Abstract

A local measure-and-reset raises the mutually unbiased correlation I2 from 1 to 3/2, refuting its monotonicity under LOCC in the fixed and the optimized reading.

**Definition 1.1 (A pair of local mutually unbiased bases).**

$$\forall d: \mathbb{N}, \forall s: \operatorname{Setting}\left(d\right), (\operatorname{A}\left(s\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right) \land A'(s) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right) \land \operatorname{B}\left(s\right) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right) \land B'(s) \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (\forall i j: \operatorname{Fin}\left(d\right), \operatorname{normSq}\left((\operatorname{A}\left(s\right)^{H} \times A'(s))(i, j)\right) = 1/d) \land (\forall i j: \operatorname{Fin}\left(d\right), \operatorname{normSq}\left((\operatorname{B}\left(s\right)^{H} \times B'(s))(i, j)\right) = 1/d)$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.Setting` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

Alice's two bases are the columns of the unitary matrices A and A', Bob's those of B and B'; the bases of each party are mutually unbiased, |⟨a_i|a'_j⟩|² = 1/d, as in §II of arXiv:2509.24045v1 ("{a', b'} ∈ B_2 which is mutually unbiased to B_1").

**Definition 1.2 (The product basis vector).**

$$\forall d: \mathbb{N}, \forall X Y: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall i: \operatorname{Fin}\left(d\right), \forall a b: \operatorname{Fin}\left(d\right), \operatorname{prodVec}\left(X, Y, i, (a, b)\right) = X(a, i) \times Y(b, i)$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.prodVec` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

The i-th column of X tensored with the i-th column of Y, so that ⟨i_a ⊗ i_b|ρ|i_a ⊗ i_b⟩ is the joint probability P_{a,b}(i,i) of Eq. (pAB).

**Definition 1.3 (The correlation I2 for a setting).**

$$\forall d: \mathbb{N}, \forall s: \operatorname{Setting}\left(d\right), \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{I2}\left(s, \rho\right) = \sum_{i} \operatorname{re}\left(\operatorname{star}\left(\operatorname{prodVec}\left(\operatorname{A}\left(s\right), \operatorname{B}\left(s\right), i\right)\right) \cdot (\rho \cdot \operatorname{prodVec}\left(\operatorname{A}\left(s\right), \operatorname{B}\left(s\right), i\right))\right) + \sum_{i} \operatorname{re}\left(\operatorname{star}\left(\operatorname{prodVec}\left(A'(s), B'(s), i\right)\right) \cdot (\rho \cdot \operatorname{prodVec}\left(A'(s), B'(s), i\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.I2` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

I2 = C_{a,b} + C_{a',b'} with C_{a,b} = sum over i of P_{a,b}(i,i) (Eq. (cAB)); the expression is linear in ρ, so p_k I2(ρ_k) equals I2 of the unnormalized branch.

**Definition 1.4 (The optimized correlation).**

$$\forall d: \mathbb{N}, \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{I2max}\left(\rho\right) = \operatorname{sup}_{s: \operatorname{Setting}\left(d\right)} \operatorname{I2}\left(s, \rho\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.I2max` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The supremum of I2 over all local settings: the paper evaluates I2 of a pure state in its Schmidt basis, and this is the state-independent version of that choice.

**Definition 1.5 (The unnormalized branch of a local instrument).**

$$\forall d: \mathbb{N}, \forall E: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), \operatorname{branch}\left(E, \rho\right) = \operatorname{kronecker}\left(E, 1\right) \times \rho \times (\operatorname{kronecker}\left(E, 1\right))^{H}$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.branch` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

Eq. (10) uses ρ_k = (E_k ⊗ I) ρ (E_k ⊗ I)† / p_k; branch E ρ is the numerator, so p_k ρ_k = branch E_k ρ, including p_k = 0.

**Definition 1.6 (Monotonicity for every fixed setting).**

$$claimFixed \Leftrightarrow (\forall d: \mathbb{N}, 2 \leq d \Rightarrow \forall s: \operatorname{Setting}\left(d\right), \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), \forall E1 E2: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{PosSemidef}\left(\rho\right) \Rightarrow \operatorname{trace}\left(\rho\right) = 1 \Rightarrow E1^{H} \times E1 + E2^{H} \times E2 = 1 \Rightarrow \operatorname{I2}\left(s, \operatorname{branch}\left(E1, \rho\right)\right) + \operatorname{I2}\left(s, \operatorname{branch}\left(E2, \rho\right)\right) \leq \operatorname{I2}\left(s, \rho\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claimFixed` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

The Conjecture of §II, "The quantity I_2 is monotonically non-increasing under LOCC operations", for the binary local instruments of Eq. (10), with I2 taken for any fixed pair of local mutually unbiased bases in any dimension d ≥ 2.

**Definition 1.7 (Monotonicity of the optimized correlation).**

$$claimOptimized \Leftrightarrow (\forall d: \mathbb{N}, 2 \leq d \Rightarrow \forall \rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), \forall E1 E2: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{PosSemidef}\left(\rho\right) \Rightarrow \operatorname{trace}\left(\rho\right) = 1 \Rightarrow E1^{H} \times E1 + E2^{H} \times E2 = 1 \Rightarrow \operatorname{I2max}\left(\operatorname{branch}\left(E1, \rho\right)\right) + \operatorname{I2max}\left(\operatorname{branch}\left(E2, \rho\right)\right) \leq \operatorname{I2max}\left(\rho\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claimOptimized` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

The same inequality for the optimized correlation I2max in every dimension d ≥ 2.

**Definition 1.8 (The conjecture in either reading).**

$$claim \Leftrightarrow (claimFixed \lor claimOptimized)$$

*Formalization.* `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claim` (`✓ std3`).

*Citation.* S. Nandi (2025). *Genuine multipartite entanglement detection with mutually unbiased bases (MUBs)*. DOI: [10.48550/arXiv.2509.24045](https://doi.org/10.48550/arXiv.2509.24045). URL: <https://arxiv.org/abs/2509.24045v1>.

*Commentary.*

The conjecture is read as the disjunction of the fixed and the optimized meaning of the quantity I2.

**Theorem 1.9 (The conjecture fails in both readings).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nandi-2025-mub-correlation-locc-refutation` (refuted) by `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nandi-2025-mub-correlation-locc-refutation","declaration_gid":"D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take d = 2, ρ = (1/2) I ⊗ |0⟩⟨0|, and Alice's instrument E₁ = |0⟩⟨0|, E₂ = |0⟩⟨1|, which measures and resets outcome 1 to |0⟩. Both branches equal (1/2)|00⟩⟨00|. For every setting I2 of ρ is 1, because each basis term is the sum over i of (1/2)|⟨b_i|0⟩|², which is 1/2 by unitarity of Bob's basis; hence I2max of ρ is 1. In the computational/Hadamard setting each branch has I2 = (1/2)(1 + 1/2) = 3/4, so the branches sum to 3/2 > 1, and the same lower bound holds for I2max.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.I2`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.I2max`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.Setting`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.branch`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claimFixed`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.claimOptimized`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.prodVec`
- Truth anchor: `D5/S3/Quantum/Entanglement/NandiMutualPredictabilityLOCCRefutation.result`
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerLocalInequivalence](../Information/BinaryStabilizerLocalInequivalence.md)
