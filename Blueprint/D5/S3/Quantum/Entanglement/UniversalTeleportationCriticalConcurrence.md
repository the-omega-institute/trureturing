# The exact critical concurrence for universal quantum teleportation

## Abstract

For every pure two-qubit input sqrt(a)|00> + sqrt(1 - a)|11> with 1/2 < a < 1, a qubit channel acting on Bob can make the shared state useful for universal quantum teleportation exactly when its initial concurrence exceeds sqrt(5 - 2 sqrt(3))/3. Necessity holds for every finite Kraus family, and a non-unital amplitude-damping channel attains sufficiency.

**Definition 1.1 (The initial pure vector).**

$$\forall a \in \mathbb{R},\; \forall p \in (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{psi}\left(a, p\right) = \operatorname{ite}\left(p = (0, 0), (\operatorname{Real}.\operatorname{sqrt}\left(a\right): \mathbb{C}), \operatorname{ite}\left(p = (1, 1), (\operatorname{Real}.\operatorname{sqrt}\left(1 - a\right): \mathbb{C}), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.psi` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

Section V uses the vector sqrt(a)|00> + sqrt(1 - a)|11>. Alice is the first qubit and Bob the second. Its only nonzero coordinates for 0 < a < 1 are sqrt(a) at (0, 0) and sqrt(1 - a) at (1, 1), viewed as complex numbers. The definition is given for every real a using Real.sqrt.

**Definition 1.2 (The initial two-qubit operator).**

$$\forall a \in \mathbb{R},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{initial}\left(a\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{PureState}.\operatorname{PureStateHandshake}.\operatorname{rankOneDensity}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{psi}\left(a\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.initial` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

The initial operator is D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity applied to psi(a), the outer product |psi(a)><psi(a)| with pointwise complex conjugation. For 0 <= a <= 1 this is a rank-one density matrix.

**Definition 1.3 (Failure to preserve the identity).**

$$\forall m \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{NonUnital}\left(K\right)) \Leftrightarrow (\sum_{k: \operatorname{Fin}\left(m\right)} (K\left(k\right) \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(K\left(k\right)\right)) \ne (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.NonUnital` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

The Kraus family is non-unital when the sum of K_k K_k adjoint differs from the identity. Thus its action on the identity does not return the identity.

**Definition 1.4 (Sending Bob's qubit through the channel).**

$$\forall m \in \mathbb{N},\; \forall a \in \mathbb{R},\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{out}\left(a, K\right) = \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Foundation}.\operatorname{FiniteKrausChannel}.\operatorname{PhyslibLeaf}.\operatorname{MatrixMap}.\operatorname{of}_{kraus}\left((\lambda (k: \operatorname{Fin}\left(m\right)) \mapsto \operatorname{Matrix}.\operatorname{kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K\left(k\right)\right)), (\lambda (k: \operatorname{Fin}\left(m\right)) \mapsto \operatorname{Matrix}.\operatorname{kronecker}\left((1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)), K\left(k\right)\right)), \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{initial}\left(a\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.out` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

Bob's channel acts on the second tensor factor. D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus is applied to two copies of the family k maps to I tensor K_k and then to the initial operator. Its action is the sum of conjugations by that family, with Matrix.kronecker denoting the tensor product of matrices.

**Definition 1.5 (Usefulness for universal quantum teleportation).**

$$\forall rho \in \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{UsefulUQT}\left(rho\right)) \Leftrightarrow (\exists U \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \exists V \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \exists t \in \mathbb{R},\; (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((V \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(2\right), \mathbb{C}\right)) \land ((\frac{1}{3} < t) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\operatorname{Matrix}.\operatorname{kronecker}\left(U, V\right) \cdot rho \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left(\operatorname{Matrix}.\operatorname{kronecker}\left(U, V\right)\right)\right) = (\lambda (i: \operatorname{Fin}\left(3\right)) (j: \operatorname{Fin}\left(3\right)) \mapsto \operatorname{ite}\left(i = j, -t, 0\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.UsefulUQT` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

There are local unitaries U and V and a real t > 1/3 for which the conjugated operator has correlation matrix -t I, with zero off-diagonal entries. The correlation matrix is D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction.corr, whose entries are the real parts of tr(rho (sigma_i tensor sigma_j)). For two-qubit states this is the source's Section II.C criterion |t11| = |t22| = |t33| > 1/3 in the canonical form of Section II.B, Eq. (3), with lambda_k = -1. The displayed definition permits any complex two-qubit operator rho.

**Definition 1.6 (The critical concurrence).**

$$\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{Cstar} = \frac{\operatorname{Real}.\operatorname{sqrt}\left(5 - 2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(3\right)\right)}{3}$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.Cstar` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

The exact threshold is sqrt(5 - 2 sqrt(3))/3 = sqrt((2/3)(4 + sqrt(3))(1 - (4 + sqrt(3))/6)), approximately 0.4131. The latter radical is the sufficient threshold after Eq. (50) in Section V.2; the source rounds it to 0.41.

**Definition 1.7 (Concurrence of the input vector).**

$$\forall a \in \mathbb{R},\; \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{conc}\left(a\right) = 2 \cdot \operatorname{Real}.\operatorname{sqrt}\left(a \cdot \left(1 - a\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.conc` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

Section V gives the initial pure-state concurrence as 2 sqrt(a(1 - a)). The function is defined for every real a; on 1/2 < a < 1 its value is strictly between zero and one.

**Definition 1.8 (The exact threshold statement).**

$$(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{claim}) \Leftrightarrow (\forall a \in \mathbb{R},\; (\frac{1}{2} < a) \Rightarrow ((a < 1) \Rightarrow ((\forall m \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{SwitchUselessConcatenationRefutation}.\operatorname{IsKrausChannel}\left(K\right)) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{UsefulUQT}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{out}\left(a, K\right)\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{Cstar} < \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{conc}\left(a\right)))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{Cstar} < \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{conc}\left(a\right)) \Rightarrow (\exists m \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{SwitchUselessConcatenationRefutation}.\operatorname{IsKrausChannel}\left(K\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{NonUnital}\left(K\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{UsefulUQT}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{out}\left(a, K\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.claim` (`✓ std3`).

*Citation.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

For each 1/2 < a < 1, every finite Kraus channel producing a useful universal-teleportation state requires concurrence strictly above Cstar. Conversely, above Cstar there is a non-unital finite Kraus channel producing such a state. This gives the precise critical value sought in Section V.2, Conjecture 1, using the source's exact radical.

**Theorem 1.9 (Necessity and non-unital attainment).**

$$\forall a \in \mathbb{R},\; (\frac{1}{2} < a) \Rightarrow ((a < 1) \Rightarrow ((\forall m \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{SwitchUselessConcatenationRefutation}.\operatorname{IsKrausChannel}\left(K\right)) \Rightarrow ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{UsefulUQT}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{out}\left(a, K\right)\right)) \Rightarrow (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{Cstar} < \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{conc}\left(a\right)))) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{Cstar} < \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{conc}\left(a\right)) \Rightarrow (\exists m \in \mathbb{N},\; \exists K \in \operatorname{Fin}\left(m\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{SwitchUselessConcatenationRefutation}.\operatorname{IsKrausChannel}\left(K\right)) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{NonUnital}\left(K\right)) \land (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{UsefulUQT}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{UniversalTeleportationCriticalConcurrence}.\operatorname{out}\left(a, K\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghosal-das-banerjee-2021-critical-concurrence-universal-teleportation` (proved) by `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghosal-das-banerjee-2021-critical-concurrence-universal-teleportation","declaration_gid":"D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arkaprabha Ghosal, Debarshi Das, Subhashish Banerjee (2021). *Characterizing qubit channels in the context of quantum teleportation*. DOI: [10.1103/PhysRevA.103.052422](https://doi.org/10.1103/PhysRevA.103.052422). URL: <https://arxiv.org/abs/2102.02054v2>.

*Commentary.*

Put r = 2a - 1, so the squared initial concurrence is 1 - r squared. Bob's trace-preserving channel leaves Alice's marginal unchanged, and local unitaries preserve the length r of Alice's Bloch vector. In a frame with correlation matrix -t I, let n be the unit direction of Alice's Bloch vector and beta Bob's Bloch component along n. Positivity of the corner on the two negative spin projections gives r + beta <= 1 - t. Cauchy-Schwarz for the positive trace form, applied to the opposite spin projections and their product with the swap matrix, gives (r - beta) squared <= (1 - t)(1 + 3t). Eliminating beta yields r squared + rt + t squared <= r + t. Since t > 1/3, this forces r < (1 + sqrt(3))/3 and hence concurrence strictly greater than Cstar.

For sufficiency take t = (1 - r + sqrt((1 - r)(1 + 3r)))/2 and gamma = (1 - t)/(1 + r). Above the concurrence threshold one has 1/3 < t < 1 and gamma > 0. The amplitude-damping Kraus pair K_0 = diag(sqrt(1 - gamma), 1), K_1 = sqrt(gamma)|1><0| is trace preserving and non-unital. The identity t squared = (1 - r)(t + r) gives output correlation matrix diag(t, -t, t); conjugating Bob by sigma_y changes it to -t I. Thus the exact threshold is sqrt(5 - 2 sqrt(3))/3, with strict inequality required for usefulness.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.Cstar`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.NonUnital`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.UsefulUQT`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.conc`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.initial`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.out`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.psi`
- Truth anchor: `D5/S3/Quantum/Entanglement/UniversalTeleportationCriticalConcurrence.result`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH](SteeringEllipsoidCHSH.md)
- Dependency: [D5/S3/QuantumChannels/SwitchUselessConcatenationRefutation](../../QuantumChannels/SwitchUselessConcatenationRefutation.md)
