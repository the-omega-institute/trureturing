# A counterexample to Fan–Wu–Fei channel coherence domination

## Abstract

A qubit measure-and-prepare channel has Choi coherence below its commutator coherence at alpha = 2.

Complex matrices use the source's computational basis and its product basis. MatrixMap denotes the complex linear maps on matrices. Real matrix powers use cfc, the real continuous functional calculus. The infimum and supremum range over all positive semidefinite matrices of trace one in the displayed spaces. Anonymous square brackets give finite enumerations and decidable equality for their index types.

**Definition 1.1 (The alpha-relative Renyi divergence at z = 1).**

$$\forall (c : Type), ([\operatorname{Fintype}\left(c\right)] [\operatorname{DecidableEq}\left(c\right)] \forall (\alpha : \mathbb{R}), (\forall (\rho : \operatorname{Matrix}\left(c, c, \mathbb{C}\right)), (\forall (\sigma : \operatorname{Matrix}\left(c, c, \mathbb{C}\right)), (\operatorname{renyiDiv}\left(\alpha, \rho, \sigma\right) = \frac{((\operatorname{RCLike}.\operatorname{re}\left(\operatorname{Matrix}.\operatorname{trace}\left(((\operatorname{cfc}\left(\lambda (x : \mathbb{R}) \mapsto ((x)^{\frac{(1) - (\alpha)}{2}}), \sigma\right)) \cdot (\operatorname{cfc}\left(\lambda (x : \mathbb{R}) \mapsto ((x)^{\alpha}), \rho\right))) \cdot (\operatorname{cfc}\left(\lambda (x : \mathbb{R}) \mapsto ((x)^{\frac{(1) - (\alpha)}{2}}), \sigma\right))\right)\right))^{\frac{1}{\alpha}}) - (1)}{(\alpha) - (1)}))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.renyiDiv` (`✓ std3`).

*Citation.* Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei (2024). *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*. DOI: [10.1007/s11128-024-04309-w](https://doi.org/10.1007/s11128-024-04309-w). URL: <https://arxiv.org/abs/2506.10796v1>.

*Commentary.*

Page 2, Eqs. (1)–(2): “D_{α,z}(ρ, σ) = (f_{α,z}(ρ, σ)^{1/α} − 1)/(α − 1)”, with “f_{α,z}(ρ, σ) = Tr (σ^{(1−α)/2z} ρ^{α/z} σ^{(1−α)/2z})^z”. Here z = 1. Matrix powers are cfc applied to the real power function, and RCLike.re takes the real part of the complex trace. The displayed formula is defined on all complex square matrices; the coherence quantities below restrict to density matrices.

**Definition 1.2 (Coherence of the normalized Choi matrix).**

$$\forall (a : Type), (\forall (b : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (\alpha : \mathbb{R}), (\forall (\varphi : \operatorname{MatrixMap}\left(a, b, \mathbb{C}\right)), (\operatorname{coherence}\left(\alpha, \varphi\right) = \operatorname{sInf}\left(\{(r : \mathbb{R}) \mid \exists (\sigma : \operatorname{Matrix}\left((a \times b), (a \times b), \mathbb{C}\right)), (((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\sigma\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(\sigma\right) = 1)) \land ((\operatorname{Matrix}.\operatorname{diagonal}\left(\lambda (i : (a \times b)) \mapsto (\sigma\left(i, i\right))\right) = \sigma) \land (r = \operatorname{renyiDiv}\left(\alpha, \lambda (p : (a \times b)) \mapsto (\lambda (q : (a \times b)) \mapsto ((((\operatorname{Fintype}.\operatorname{card}\left(a\right) : \mathbb{C}))^{-1}) \cdot (\varphi\left(\operatorname{Matrix}.\operatorname{single}\left(p.1, q.1, 1\right), p.2, q.2\right)))), \sigma\right))))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.coherence` (`✓ std3`).

*Citation.* Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei (2024). *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*. DOI: [10.1007/s11128-024-04309-w](https://doi.org/10.1007/s11128-024-04309-w). URL: <https://arxiv.org/abs/2506.10796v1>.

*Commentary.*

Page 4, Definition 2, Eq. (7): “C_{α,z}(φ) = min_{φ̃ ∈ IC_AB} D_{α,z}(φ, φ̃) = min_{M_φ̃ ∈ I} (f^{1/α}_{α,z}(M_φ, M_φ̃) − 1)/(α − 1)”. The formula takes z = 1 and expresses the minimum as a real infimum over diagonal density matrices on a × b. The normalized Choi entry at (i,j),(k,l) is (card a)⁻¹ φ(single i k 1) j l. Its scalar factor is complex; it equals 1/2 for the qubit input used in the counterexample.

**Definition 1.3 (Coherence from the two orders of dephasing).**

$$\forall (a : Type), (\forall (b : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (\alpha : \mathbb{R}), (\forall (\varphi : \operatorname{MatrixMap}\left(a, b, \mathbb{C}\right)), (\operatorname{commutativityCoherence}\left(\alpha, \varphi\right) = \operatorname{sSup}\left(\{(r : \mathbb{R}) \mid \exists (\rho : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \land (\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = 1)) \land (r = \operatorname{renyiDiv}\left(\alpha, \varphi\left(\operatorname{Matrix}.\operatorname{diagonal}\left(\lambda (i : a) \mapsto (\rho\left(i, i\right))\right)\right), \operatorname{Matrix}.\operatorname{diagonal}\left(\lambda (i : b) \mapsto (\varphi\left(\rho, i, i\right))\right)\right)))\}\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.commutativityCoherence` (`✓ std3`).

*Citation.* Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei (2024). *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*. DOI: [10.1007/s11128-024-04309-w](https://doi.org/10.1007/s11128-024-04309-w). URL: <https://arxiv.org/abs/2506.10796v1>.

*Commentary.*

Page 7, Definition 4, Eq. (10): “C̃_{α,z}(φ) = sup_ρ D_{α,z}(φ ∘ ∆_A(ρ), ∆_B ∘ φ(ρ)) … the supremum in Eq. (10) is taken over all quantum states.” At z = 1, the input is any density matrix on a. Dephasing retains the diagonal entries, as in Eq. (9), and occurs before or after φ in the two arguments.

**Definition 1.4 (The proposed domination for every channel).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (a : Type), (\forall (b : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (\varphi : \operatorname{MatrixMap}\left(a, b, \mathbb{C}\right)), ((\operatorname{IsCompletelyPositive}\left(\varphi\right)) \Rightarrow ((\forall (x : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{trace}\left(\varphi\left(x\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left(x\right))) \Rightarrow (\forall (\alpha : \mathbb{R}), ((((0 < \alpha) \land (\alpha < 1)) \lor ((1 < \alpha) \land (\alpha \le 2))) \Rightarrow (\operatorname{commutativityCoherence}\left(\alpha, \varphi\right) \le \operatorname{coherence}\left(\alpha, \varphi\right)))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.claim` (`✓ std3`).

*Citation.* Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei (2024). *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*. DOI: [10.1007/s11128-024-04309-w](https://doi.org/10.1007/s11128-024-04309-w). URL: <https://arxiv.org/abs/2506.10796v1>.

*Commentary.*

Page 8, Section 3: “From the examples in the next section and numerical results, it is conjectured that C_{α,1}(φ) ≥ C̃_{α,1}(φ) holds for all quantum channels φ, but we have not yet found a proof.” The finite input and output types are a and b; φ is completely positive and preserves the trace of every matrix. The range of α is (0,1) ∪ (1,2], as in Eq. (8). The comparison is written with the commutator quantity on the left.

**Theorem 1.5 (Two prepared outputs refute the universal comparison).**

$$\neg (\forall (a : Type), (\forall (b : Type), ([\operatorname{Fintype}\left(a\right)] [\operatorname{DecidableEq}\left(a\right)] [\operatorname{Fintype}\left(b\right)] [\operatorname{DecidableEq}\left(b\right)] \forall (\varphi : \operatorname{MatrixMap}\left(a, b, \mathbb{C}\right)), ((\operatorname{IsCompletelyPositive}\left(\varphi\right)) \Rightarrow ((\forall (x : \operatorname{Matrix}\left(a, a, \mathbb{C}\right)), (\operatorname{Matrix}.\operatorname{trace}\left(\varphi\left(x\right)\right) = \operatorname{Matrix}.\operatorname{trace}\left(x\right))) \Rightarrow (\forall (\alpha : \mathbb{R}), ((((0 < \alpha) \land (\alpha < 1)) \lor ((1 < \alpha) \land (\alpha \le 2))) \Rightarrow (\operatorname{commutativityCoherence}\left(\alpha, \varphi\right) \le \operatorname{coherence}\left(\alpha, \varphi\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result` (`✓ std3`). ∎

*Resolves.* `Problems/fan-wu-fei-2024-channel-coherence-domination` (refuted) by `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fan-wu-fei-2024-channel-coherence-domination","declaration_gid":"D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei (2024). *Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy*. DOI: [10.1007/s11128-024-04309-w](https://doi.org/10.1007/s11128-024-04309-w). URL: <https://arxiv.org/abs/2506.10796v1>.

*Commentary.*

Take σ_t = [[1/2,t/2],[t/2,1/2]] and φ(X) = X(0,0) σ_{3/4} + X(1,1) σ_{1/2}. Sixteen rational Kraus operators establish complete positivity, and the output trace equals the input trace. The normalized Choi matrix M satisfies re(trace(M M)) = 45/128. The diagonal density matrix I/4 gives coherence(2,φ) ≤ sqrt(45/32) − 1. Every input density matrix gives commutator divergence at most 1/4, and the input diagonal(1,0) attains 1/4. Thus commutativityCoherence(2,φ) ≥ 1/4. Finally sqrt(45/32) − 1 < 1/4, contradicting the displayed universal statement.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.coherence`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.commutativityCoherence`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.renyiDiv`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination.result`
- Dependency: [D5/S3/Quantum/Decoherence/ProjectedUnistochasticDynamics](../Decoherence/ProjectedUnistochasticDynamics.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausRepresentation](../Foundation/FiniteKrausRepresentation.md)
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../Matrix/SpectralPower.md)
