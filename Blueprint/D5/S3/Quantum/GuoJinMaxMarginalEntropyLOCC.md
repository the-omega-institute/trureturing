# Maximum marginal entropy can increase under a local measurement

## Abstract

A local measurement on a four-party pure state increases the average maximum single-party entropy.

**Definition 1.1 (The one-party reduced matrix).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall psi \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{marginal}\left(psi, i\right) = \operatorname{CStarMatrix.ofMatrix}\left(\operatorname{fun} (a: \operatorname{Fin}\left(d\right)) \mapsto (\operatorname{fun} (b: \operatorname{Fin}\left(d\right)) \mapsto (\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{ite}\left(x\left(i\right) = a, (psi\left(x\right)) \cdot (\operatorname{star}\left(psi\left(\operatorname{Function.update}\left(x, i, b\right)\right)\right)), (0: \mathbb{C})\right))))\right)$$

*Formalization.* `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.marginal` (`✓ std3`).

*Citation.* Y. Guo; Z.-X. Jin (2025). *Measure of entanglement and the monogamy relation: a topical review*. DOI: [10.48550/arXiv.2512.21992](https://doi.org/10.48550/arXiv.2512.21992). URL: <https://arxiv.org/abs/2512.21992v1>.

*Commentary.*

The amplitude function is indexed by basis tuples Fin n → Fin d. The matrix entry sums ψ(x) times the conjugate of ψ(x[i ↦ b]) over tuples with x(i) = a. This is the reduced density matrix of party i for a normalized pure state.

**Definition 1.2 (The largest single-party entropy).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall psi \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \operatorname{maxMarginalEntropy}\left(psi\right) = \operatorname{iSup}\left(\operatorname{fun} (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{-\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{marginal}\left(psi, i\right)) \cdot (\operatorname{CFC.log}\left(\operatorname{marginal}\left(psi, i\right)\right))\right)\right)}{\operatorname{Real.log}\left((2: \mathbb{R})\right)})\right)$$

*Formalization.* `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.maxMarginalEntropy` (`✓ std3`).

*Citation.* Y. Guo; Z.-X. Jin (2025). *Measure of entanglement and the monogamy relation: a topical review*. DOI: [10.48550/arXiv.2512.21992](https://doi.org/10.48550/arXiv.2512.21992). URL: <https://arxiv.org/abs/2512.21992v1>.

*Commentary.*

Pages 87–88, Eq. (189): “The quantity E′^(n)(|ψ⟩) = max_i h(ρ^{A_i}) can reports the amount of entanglement contained in |ψ⟩ to some extent [168]: If it is nonincreasing on average under LOCC, then (i) E′^(3) is a complete global MEM but not tightly complete monogamous, and if h is strictly concave, E′^(3) is completely monogamous, and (ii) E′^(n) is not complete whenever n ≥ 4.” Table 16 includes h = S. Page 14, Section 2: “S(ρ) = −Tr(ρ log₂ ρ) is the von Neumann entropy of the state ρ”. CFC.log is the operator logarithm on CStarMatrix; division by Real.log 2 gives entropy in bits. The expression is defined on all matrices and represents entropy for positive trace-one matrices. The real iSup over Fin n represents this maximum for a nonempty finite collection of parties.

**Definition 1.3 (A local Kraus operator on amplitudes).**

$$\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall K \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall psi \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \operatorname{applyLocal}\left(K, i, psi\right) = \operatorname{fun} (x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)) \mapsto (\sum_{a: \operatorname{Fin}\left(d\right)} ((K\left(x\left(i\right), a\right)) \cdot (psi\left(\operatorname{Function.update}\left(x, i, a\right)\right))))$$

*Formalization.* `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.applyLocal` (`✓ std3`).

*Citation.* Y. Guo; Z.-X. Jin (2025). *Measure of entanglement and the monogamy relation: a topical review*. DOI: [10.48550/arXiv.2512.21992](https://doi.org/10.48550/arXiv.2512.21992). URL: <https://arxiv.org/abs/2512.21992v1>.

*Commentary.*

K acts on the i-th coordinate of a basis tuple. Its row x(i) is contracted with the amplitudes obtained by replacing that coordinate with a. All other coordinates stay fixed.

**Definition 1.4 (The proposed average monotonicity).**

$$\operatorname{claim} = \left(\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall psi \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(psi\left(x\right)\right)) = (1: \mathbb{R})) \Rightarrow ((\sum_{r: \operatorname{Fin}\left(m\right)} ((\operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right)) \cdot (K\left(r\right))) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))) \Rightarrow (\sum_{r: \operatorname{Fin}\left(m\right)} (\operatorname{ite}\left(\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right)) = (0: \mathbb{R}), (0: \mathbb{R}), (\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right))) \cdot (\operatorname{maxMarginalEntropy}\left(\operatorname{HSMul.hSMul}\left((\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right))\right)\right))^{-1}, \operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\right)\right))\right)) \le \operatorname{maxMarginalEntropy}\left(psi\right)))\right)$$

*Formalization.* `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.claim` (`✓ std3`).

*Citation.* Y. Guo; Z.-X. Jin (2025). *Measure of entanglement and the monogamy relation: a topical review*. DOI: [10.48550/arXiv.2512.21992](https://doi.org/10.48550/arXiv.2512.21992). URL: <https://arxiv.org/abs/2512.21992v1>.

*Commentary.*

Page 88, Section 9.4: “Note here that we can not prove here E′^(n) is nonincreasing on average under LOCC, but we conjecture that E′^(n) does not increase on average under LOCC for these cases mentioned above. Hereafter we always assume the conjecture is true.” Here n counts parties, d is their common local dimension, and m counts measurement outcomes. The input has squared norm one. The Kraus operators obey ∑ᵣ Kᵣ†Kᵣ = 1. A branch has probability equal to its squared norm, is normalized by the inverse square root of that probability, and contributes zero when the probability is zero. The formula states the consequence for one local measurement.

**Theorem 1.5 (A four-party counterexample).**

$$\neg (\forall n \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall psi \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)\right) \to \mathbb{C},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(psi\left(x\right)\right)) = (1: \mathbb{R})) \Rightarrow ((\sum_{r: \operatorname{Fin}\left(m\right)} ((\operatorname{Matrix.conjTranspose}\left(K\left(r\right)\right)) \cdot (K\left(r\right))) = (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))) \Rightarrow (\sum_{r: \operatorname{Fin}\left(m\right)} (\operatorname{ite}\left(\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right)) = (0: \mathbb{R}), (0: \mathbb{R}), (\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right))) \cdot (\operatorname{maxMarginalEntropy}\left(\operatorname{HSMul.hSMul}\left((\operatorname{Complex.ofReal}\left(\operatorname{Real.sqrt}\left(\sum_{x: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(\operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\left(x\right)\right))\right)\right))^{-1}, \operatorname{applyLocal}\left(K\left(r\right), i, psi\right)\right)\right))\right)) \le \operatorname{maxMarginalEntropy}\left(psi\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Y. Guo; Z.-X. Jin (2025). *Measure of entanglement and the monogamy relation: a topical review*. DOI: [10.48550/arXiv.2512.21992](https://doi.org/10.48550/arXiv.2512.21992). URL: <https://arxiv.org/abs/2512.21992v1>.

*Commentary.*

Take four parties of local dimension nine. The pure amplitude is 1/4 on the sixteen tuples (0,0,j,j) and (j,j,0,0), with j = 1,…,8, and zero elsewhere. Every initial marginal is diagonal with entries 1/2,1/16,…,1/16, so its entropy is 5/2. On party zero, the projectors Matrix.diagonal (Pi.single 0 1) and its complement give two branches of probability 1/2. In the first normalized branch, party two has diagonal marginal (0,1/8,…,1/8); in the second, party zero has that marginal. Each outcome maximum is therefore at least 3, and their average exceeds 5/2. The maximizing party can depend on the outcome. The theorem does not assert an upper bound on either outcome maximum or settle the three-party case.

## References

- Truth anchor: `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.applyLocal`
- Truth anchor: `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.claim`
- Truth anchor: `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.marginal`
- Truth anchor: `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.maxMarginalEntropy`
- Truth anchor: `D5/S3/Quantum/GuoJinMaxMarginalEntropyLOCC.result`
- Dependency: [D5/S3/Quantum/Divergence/ThreeByThreeModulusEntropy](Divergence/ThreeByThreeModulusEntropy.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoCMIRefutation](Information/ChenKatoBrandaoCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation](Information/NoisyGraphStateCoherentInformationRefutation.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate](../Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate.md)
