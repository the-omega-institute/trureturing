# Mayer zero fidelity and process fidelity

## Abstract

The product SIC states test an n-qubit channel through their survival probabilities. Process fidelity tests the same channel on one half of a maximally entangled state.

**Definition 1.1 (Qubit SIC vectors).**

$$\forall s \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right),\; \operatorname{IsQubitSIC}\left(s\right) \Leftrightarrow ((\forall k \in \operatorname{Fin}\left(4\right),\; \operatorname{inner}\left(s\left(k\right), s\left(k\right)\right) = 1) \land (\forall k \in \operatorname{Fin}\left(4\right),\; \forall l \in \operatorname{Fin}\left(4\right),\; (\neg k = l) \Rightarrow (\left\lVert \operatorname{inner}\left(s\left(k\right), s\left(l\right)\right) \right\rVert^{2} = \frac{1}{3})))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.IsQubitSIC` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

The normalization uses the Hermitian inner product on the two complex coordinates. Each pair of distinct vectors has squared overlap one third.

**Theorem 1.2 (The symmetric second moment).**

$$\forall s \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right),\; (\operatorname{IsQubitSIC}\left(s\right)) \Rightarrow (\sum_{k:\operatorname{Fin}\left(4\right)} \operatorname{tensor}\left(\operatorname{rankOneDensity}\left(s\left(k\right)\right), \operatorname{rankOneDensity}\left(s\left(k\right)\right)\right) = (\frac{2}{3}) \cdot ((1) + (\operatorname{swapMatrix})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.sic_frame` (`✓ std3`). ∎

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

Write Pk for the outer product of the kth vector with its conjugate. The trace of the square of their tensor sum is sixteen thirds. Its trace against identity plus exchange is eight, and the square of identity plus exchange has trace twelve. Consequently, the squared Hilbert-Schmidt norm of the difference from two thirds times identity plus exchange vanishes.

**Theorem 1.3 (Bilinear second moments).**

$$\forall s \in \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right),\; (\operatorname{IsQubitSIC}\left(s\right)) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \sum_{k:\operatorname{Fin}\left(4\right)} (\operatorname{trace}\left((\operatorname{rankOneDensity}\left(s\left(k\right)\right)) \cdot (A)\right)) \cdot (\operatorname{trace}\left((\operatorname{rankOneDensity}\left(s\left(k\right)\right)) \cdot (B)\right)) = (\frac{2}{3}) \cdot (((\operatorname{trace}\left(A\right)) \cdot (\operatorname{trace}\left(B\right))) + (\operatorname{trace}\left((A) \cdot (B)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.sic_bilinear` (`✓ std3`). ∎

*Citation.* J. M. Renes, R. Blume-Kohout, A. J. Scott, C. M. Caves (2004). *Symmetric Informationally Complete Quantum Measurements*. DOI: [10.1063/1.1737053](https://doi.org/10.1063/1.1737053). URL: <https://arxiv.org/abs/quant-ph/0310075v1>.

*Commentary.*

The exchange matrix is the swapMatrix of CompositeConeProperness. Contracting the second moment with the tensor product of two arbitrary matrices gives the trace identity. The exchange term contributes the trace of their product.

**Definition 1.4 (Product SIC states).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; \forall k \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right),\; \forall x \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right),\; \operatorname{productState}\left(s, k\right)\left(x\right) = \prod_{i:\operatorname{Fin}\left(n\right)} s\left(i\right)\left(k\left(i\right)\right)\left(x\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.productState` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

At each position a label chooses one of four single-qubit SIC vectors. The coordinate of their tensor product is the product of their coordinates.

**Definition 1.5 (Zero fidelity).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{zeroFidelity}\left(s, K\right) = (\frac{1}{\left(2^{n}\right)^{2}}) \cdot (\sum_{k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)} \operatorname{real}\left(\operatorname{inner}\left(\operatorname{productState}\left(s, k\right), \operatorname{mulVec}\left(\operatorname{kraus}\left(K, \operatorname{rankOneDensity}\left(\operatorname{productState}\left(s, k\right)\right)\right), \operatorname{productState}\left(s, k\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.zeroFidelity` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

For d equal to two to the power n, zero fidelity is d to the power minus two times the sum of the survival probabilities over all product SIC labels. The channel acts by the sum of Kj rho Kj conjugate transpose.

**Definition 1.6 (Process fidelity).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{processFidelity}\left(K\right) = \operatorname{real}\left(\operatorname{inner}\left(\operatorname{maxEntangledVector}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right), \operatorname{mulVec}\left(\operatorname{kraus}\left(\operatorname{liftKraus}\left(K\right), \operatorname{maxEntangled}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right)\right), \operatorname{maxEntangledVector}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.processFidelity` (`✓ std3`).

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

The channel acts on the second register, with Kraus operators identity tensor Kj. Process fidelity is the expectation of the resulting density matrix in the maxEntangledVector of PeritoTsirelson on the qubit register. Its rank-one matrix is maxEntangled.

**Definition 1.7 (Pauli support of weight at most one).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{HasWeightOneSupport}\left(K\right) \Leftrightarrow (\forall j \in \operatorname{Fin}\left(r\right),\; \forall b \in \operatorname{Fin}\left(n\right) \to \operatorname{Pauli},\; (2 \le \operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)) \Rightarrow (\operatorname{trace}\left((\operatorname{adjoint}\left(\operatorname{wordOp}\left(b\right)\right)) \cdot (K\left(j\right))\right) = 0))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.HasWeightOneSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pauli weight is the Hamming distance from the constant identity word. Every Kraus operator has zero Hilbert-Schmidt coefficient on every Pauli string of weight at least two. Equivalently, each operator belongs to the span of identity and the three single-position Pauli operators at every position.

**Theorem 1.8 (Product Pauli moments).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall b \in \operatorname{Fin}\left(n\right) \to \operatorname{Pauli},\; \forall c \in \operatorname{Fin}\left(n\right) \to \operatorname{Pauli},\; \sum_{k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)} (\operatorname{trace}\left((\operatorname{rankOneDensity}\left(\operatorname{productState}\left(s, k\right)\right)) \cdot (\operatorname{wordOp}\left(b\right))\right)) \cdot (\operatorname{trace}\left((\operatorname{rankOneDensity}\left(\operatorname{productState}\left(s, k\right)\right)) \cdot (\operatorname{wordOp}\left(c\right))\right)) = (\operatorname{indicator}\left(b = c\right)) \cdot ((4^{n}) \cdot (\frac{1}{3}^{\operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.product_pauli_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rank-one density matrix of a product vector is the tensor product of its single-qubit projectors. Its Pauli expectation therefore factors position by position. The bilinear SIC moment gives four for the identity factor, four thirds for a matching nonidentity factor, and zero for unequal factors. Multiplying these moments gives the stated covariance.

**Theorem 1.9 (The Pauli second-moment expansion).**

$$\forall n \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \sum_{k:\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)} \left\lVert \operatorname{trace}\left((\operatorname{rankOneDensity}\left(\operatorname{productState}\left(s, k\right)\right)) \cdot (A)\right) \right\rVert^{2} = \sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} (\frac{1}{3}^{\operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)}) \cdot (\left\lVert \operatorname{trace}\left((\operatorname{wordOp}\left(b\right)) \cdot (A)\right) \right\rVert^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.product_pauli_parseval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand an arbitrary matrix in the orthogonal Pauli basis. The word_hermitian lemma of StabilizerPovmMaximalEntanglementRefutation states that every Pauli word is Hermitian, so its expectations in pure states are real. Expanding the squared modulus produces a double sum of Pauli coefficients; the product covariance removes all unequal pairs. Its factor four to the power n cancels the squared inverse dimension in the coefficients, leaving one third to the Pauli weight times each squared trace coefficient.

**Theorem 1.10 (Kraus survival amplitudes).**

$$\forall a \in \operatorname{finiteSet},\; \forall r \in \mathbb{N},\; \forall v \in a \to \mathbb{C},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(a, a, \mathbb{C}\right),\; \operatorname{real}\left(\operatorname{inner}\left(v, \operatorname{mulVec}\left(\operatorname{kraus}\left(K, \operatorname{rankOneDensity}\left(v\right)\right), v\right)\right)\right) = \sum_{j:\operatorname{Fin}\left(r\right)} \left\lVert \operatorname{inner}\left(v, \operatorname{mulVec}\left(K\left(j\right), v\right)\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.kraus_survival` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each Kraus term maps a pure projector to the projector of the transformed vector. Its expectation in the original vector is the squared modulus of their inner product. Additivity gives the sum over the Kraus family.

**Theorem 1.11 (Bell amplitude of an operator).**

$$\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{inner}\left(\operatorname{maxEntangledVector}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right), \operatorname{mulVec}\left(\operatorname{tensor}\left(1, A\right), \operatorname{maxEntangledVector}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)\right)\right)\right) = \frac{\operatorname{trace}\left(A\right)}{2^{n}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.bell_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximally entangled trace contraction with identity on the first register gives the operator trace divided by the register dimension, which is two to the power n.

**Theorem 1.12 (Total Pauli probability).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \Rightarrow (\sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} (\frac{1}{\left(2^{n}\right)^{2}}) \cdot (\sum_{j:\operatorname{Fin}\left(r\right)} \left\lVert \operatorname{trace}\left((\operatorname{wordOp}\left(b\right)) \cdot (K\left(j\right))\right) \right\rVert^{2}) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.pauli_total_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pauli expansion gives the sum of squared trace coefficients as d times the Hilbert-Schmidt squared norm of each Kraus operator. Trace preservation makes the sum of those norms equal to d. Division by d squared gives total probability one.

**Theorem 1.13 (The weighted probability bound).**

$$\forall n \in \mathbb{N},\; \forall q \in \left(\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}\right) \to \mathbb{R},\; ((\forall b \in \operatorname{Fin}\left(n\right) \to \operatorname{Pauli},\; 0 \le q\left(b\right)) \land (\sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} q\left(b\right) = 1)) \Rightarrow (((1) - ((\frac{3}{2}) \cdot ((1) - (\sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} (\frac{1}{3}^{\operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)}) \cdot (q\left(b\right))))) \le q\left(\operatorname{identityWord}\left(n\right)\right)) \land (q\left(\operatorname{identityWord}\left(n\right)\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (\sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} (\frac{1}{3}^{\operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)}) \cdot (q\left(b\right))))) \Leftrightarrow (\forall b \in \operatorname{Fin}\left(n\right) \to \operatorname{Pauli},\; (2 \le \operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)) \Rightarrow (q\left(b\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.weight_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gap is a sum of nonnegative probability terms. The coefficient vanishes at weights zero and one, and is strictly positive at every weight at least two. The gap vanishes exactly when every such probability vanishes.

**Theorem 1.14 (Process fidelity in trace coordinates).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{processFidelity}\left(K\right) = (\frac{1}{\left(2^{n}\right)^{2}}) \cdot (\sum_{j:\operatorname{Fin}\left(r\right)} \left\lVert \operatorname{trace}\left(K\left(j\right)\right) \right\rVert^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.process_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the Kraus survival identity to the normalized Bell vector and then use its operator amplitude. The resulting fidelity is the sum of squared Kraus traces divided by d squared.

**Theorem 1.15 (Zero fidelity in Pauli coordinates).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{zeroFidelity}\left(s, K\right) = \sum_{b:\operatorname{Fin}\left(n\right) \to \operatorname{Pauli}} (\frac{1}{3}^{\operatorname{hammingDist}\left(b, \lambda i \mapsto \operatorname{I}\right)}) \cdot ((\frac{1}{\left(2^{n}\right)^{2}}) \cdot (\sum_{j:\operatorname{Fin}\left(r\right)} \left\lVert \operatorname{trace}\left((\operatorname{wordOp}\left(b\right)) \cdot (K\left(j\right))\right) \right\rVert^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.zero_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the Kraus survival identity to every product SIC vector. The Pauli second moment and interchange of the two finite sums give one third to the Pauli weight times the normalized coefficient probability.

**Theorem 1.16 (Lower bound and its equality cases).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \Rightarrow (((1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \le \operatorname{processFidelity}\left(K\right)) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \Leftrightarrow (\operatorname{HasWeightOneSupport}\left(K\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.channel_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace preservation supplies a nonnegative Pauli probability distribution. Process fidelity is its identity probability, and zero fidelity is its weighted sum. The scalar bound gives the lower inequality. Equality requires every coefficient probability of weight at least two to vanish; a sum of squared moduli vanishes precisely when every individual Kraus trace coefficient vanishes.

**Theorem 1.17 (A channel attaining every permitted fidelity).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall f \in \mathbb{R},\; (\frac{1}{3} \le f) \Rightarrow ((f \le 1) \Rightarrow (\exists r \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \land ((\operatorname{zeroFidelity}\left(s, K\right) = f) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (f)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.tight_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose p equal to three f minus one divided by two and t equal to one minus p divided by three. Both parameters are nonnegative. The Kraus operators are square root p times identity and square root t times each of the three Pauli operators on position zero. Their squared operators sum to identity. Every Kraus word has weight at most one: every Pauli coefficient of higher weight has a traceless factor at another position. The three nonidentity Kraus traces vanish, so process fidelity is p. The equality characterization then forces zero fidelity to equal f.

**Theorem 1.18 (Mayer's lower inequality).**

$$\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow (\forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \Rightarrow ((1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \le \operatorname{processFidelity}\left(K\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.lower_bound` (`✓ std3`). ∎

*Citation.* K. Mayer (2021). *A short note on the 0-fidelity*. DOI: [10.48550/arXiv.2109.09629](https://doi.org/10.48550/arXiv.2109.09629). URL: <https://arxiv.org/abs/2109.09629v1>.

*Commentary.*

The lower inequality in Theorem 1 bounds the process fidelity by one minus three halves of the zero infidelity.

**Definition 1.19 (The sharp lower bound).**

$$\operatorname{claim} \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow ((\forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \Rightarrow (((1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \le \operatorname{processFidelity}\left(K\right)) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \Leftrightarrow (\operatorname{HasWeightOneSupport}\left(K\right))))) \land (\forall f \in \mathbb{R},\; (\frac{1}{3} \le f) \Rightarrow ((f \le 1) \Rightarrow (\exists r \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \land ((\operatorname{zeroFidelity}\left(s, K\right) = f) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (f)))))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive number of qubits and every choice of local SIC vectors, the lower bound has equality precisely for Kraus operators of Pauli weight at most one. Every zero fidelity between one third and one is to be attained at that bound.

**Theorem 1.20 (Tightness in every qubit dimension).**

$$\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\forall s \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{C}\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{IsQubitSIC}\left(s\left(i\right)\right)) \Rightarrow ((\forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \Rightarrow (((1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \le \operatorname{processFidelity}\left(K\right)) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (\operatorname{zeroFidelity}\left(s, K\right)))) \Leftrightarrow (\operatorname{HasWeightOneSupport}\left(K\right))))) \land (\forall f \in \mathbb{R},\; (\frac{1}{3} \le f) \Rightarrow ((f \le 1) \Rightarrow (\exists r \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\sum_{j:\operatorname{Fin}\left(r\right)} (\operatorname{adjoint}\left(K\left(j\right)\right)) \cdot (K\left(j\right)) = 1) \land ((\operatorname{zeroFidelity}\left(s, K\right) = f) \land (\operatorname{processFidelity}\left(K\right) = (1) - ((\frac{3}{2}) \cdot ((1) - (f))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.result` (`✓ std3`). ∎

*Resolves.* `Problems/mayer-2021-zero-fidelity-tightness` (proved) by `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mayer-2021-zero-fidelity-tightness","declaration_gid":"D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every positive number of qubits and every choice of local SIC vectors, the process fidelity is bounded below by one minus three halves of the zero infidelity. Equality holds precisely when all Kraus coefficients on Pauli words of weight at least two vanish. Noise acting on one qubit supplies a trace-preserving Kraus family that attains this bound at every zero fidelity from one third to one.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.HasWeightOneSupport`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.IsQubitSIC`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.bell_amplitude`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.channel_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.kraus_survival`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.lower_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.pauli_total_mass`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.processFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.process_trace`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.productState`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.product_pauli_covariance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.product_pauli_parseval`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.sic_bilinear`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.sic_frame`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.tight_channel`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.weight_bound`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.zeroFidelity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/MayerZeroFidelityTightness.zero_trace`
- Dependency: [D5/S3/Quantum/Measurement/ExactConditionalPreparationCost](../Measurement/ExactConditionalPreparationCost.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../../QuantumBounds/PeritoTsirelson.md)
- Dependency: [D5/S3/Resource/CompositeConeProperness](../../Resource/CompositeConeProperness.md)
