# Refutation of the geometric tangle ansatz

## Abstract

A type-4c canonical state on the Bloch-norm diagonal refutes the Benedito–Sierra geometric tangle ansatz.

**Definition 1.1 (Canonical five-term three-qubit state).**

$$CanonicalState = \{lambda0:\mathbb{R}, lambda1:\mathbb{R}, lambda2:\mathbb{R}, lambda3:\mathbb{R}, lambda4:\mathbb{R}, phi:\mathbb{R}\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.CanonicalState` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The paper prints verbatim: “|ψ⟩ overset{CD}{→} |λ₀, λ⃗, λ₄; φ⟩ := [ λ₀|000⟩ + λ₁ e^{iφ}|100⟩ + λ₂|101⟩ + λ₃|110⟩ + λ₄|111⟩ ] where λⱼ ∈ [0,1] ∀ j; Σⱼ₌₀⁴ λⱼ² = 1; φ ∈ [0,π].” (arXiv v2, p. 3, Eqs. (3)–(4)). This is the six-parameter canonical state carrier used below.

**Definition 1.2 (Canonical parameter conditions).**

$$\forall psi \in CanonicalState,\; (isCanonical\left(psi\right)) \Leftrightarrow (\left(\left(0 \le lambda0\left(psi\right) \land lambda0\left(psi\right) \le 1\right) \land \left(\left(0 \le lambda1\left(psi\right) \land lambda1\left(psi\right) \le 1\right) \land \left(\left(0 \le lambda2\left(psi\right) \land lambda2\left(psi\right) \le 1\right) \land \left(\left(0 \le lambda3\left(psi\right) \land lambda3\left(psi\right) \le 1\right) \land \left(0 \le lambda4\left(psi\right) \land lambda4\left(psi\right) \le 1\right)\right)\right)\right)\right) \land \left(lambda0\left(psi\right)^{2} + lambda1\left(psi\right)^{2} + lambda2\left(psi\right)^{2} + lambda3\left(psi\right)^{2} + lambda4\left(psi\right)^{2} = 1 \land \left(0 \le phi\left(psi\right) \land phi\left(psi\right) \le \pi\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isCanonical` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The five amplitudes lie in [0,1], their squares sum to one, and the phase lies in [0,π].

**Definition 1.3 (Complex coefficient tensor).**

$$\forall psi \in CanonicalState,\; amplitudes\left(psi, 0, 0, 0\right) = lambda0\left(psi\right) \land \left(amplitudes\left(psi, 0, 0, 1\right) = 0 \land \left(amplitudes\left(psi, 0, 1, 0\right) = 0 \land \left(amplitudes\left(psi, 0, 1, 1\right) = 0 \land \left(amplitudes\left(psi, 1, 0, 0\right) = lambda1\left(psi\right) \cdot exp\left(phi\left(psi\right) \cdot i\right) \land \left(amplitudes\left(psi, 1, 0, 1\right) = lambda2\left(psi\right) \land \left(amplitudes\left(psi, 1, 1, 0\right) = lambda3\left(psi\right) \land amplitudes\left(psi, 1, 1, 1\right) = lambda4\left(psi\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.amplitudes` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The eight coefficients are listed in lexicographic qubit order A, B, C. The phase occurs only in the coefficient λ₁ exp(iφ).

**Definition 1.4 (Pure-state density matrix).**

$$\forall psi \in CanonicalState,\; \forall a \in Fin\left(2\right),\; \forall b \in Fin\left(2\right),\; \forall c \in Fin\left(2\right),\; \forall d \in Fin\left(2\right),\; \forall e \in Fin\left(2\right),\; \forall f \in Fin\left(2\right),\; jointDensity\left(psi, (a,(b,c)), (d,(e,f))\right) = amplitudes\left(psi, a, b, c\right) \cdot conj\left(amplitudes\left(psi, d, e, f\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.jointDensity` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The outer product |ψ⟩⟨ψ| has entries t_ijk conjugate(t_i'j'k') on A × (B × C).

**Definition 1.5 (The A marginal).**

$$\forall psi \in CanonicalState,\; rhoA\left(psi\right) = partialTraceRight\left(jointDensity\left(psi\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoA` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

Tracing B and C means summing t_ijk conjugate(t_i'jk) over j,k ∈ Fin 2.

**Definition 1.6 (The B marginal).**

$$\forall psi \in CanonicalState,\; rhoB\left(psi\right) = partialTraceRight\left(partialTraceLeft\left(jointDensity\left(psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoB` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

First trace A, then C: the entries are the sum of t_ijk conjugate(t_ij'k) over i,k ∈ Fin 2.

**Definition 1.7 (The C marginal).**

$$\forall psi \in CanonicalState,\; rhoC\left(psi\right) = partialTraceLeft\left(partialTraceLeft\left(jointDensity\left(psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoC` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

First trace A, then B: the entries are the sum of t_ijk conjugate(t_ijk') over i,j ∈ Fin 2.

**Definition 1.8 (Reduced-state Bloch vectors).**

$$\forall psi \in CanonicalState,\; blochVectors\left(psi, 0\right) = bloch\left(rhoA\left(psi\right)\right) \land \left(blochVectors\left(psi, 1\right) = bloch\left(rhoB\left(psi\right)\right) \land blochVectors\left(psi, 2\right) = bloch\left(rhoC\left(psi\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.blochVectors` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The frozen bloch map extracts (2 Re ρ₀₁, −2 Im ρ₀₁, Re ρ₀₀ − Re ρ₁₁), the coordinates in ρ = (I + r·σ)/2. For the canonical state, A has y = 2λ₀λ₁ sin φ, while B and C have y = −2λ₁λ₃ sin φ and −2λ₁λ₂ sin φ. The coordinate identities are established inside the refutation.

**Definition 1.9 (Cayley hyperdeterminant).**

$$\forall t \in Fin\left(2\right) \to \left(Fin\left(2\right) \to \left(Fin\left(2\right) \to \mathbb{C}\right)\right),\; cayley\left(t\right) = t\left(0, 0, 0\right)^{2} \cdot t\left(1, 1, 1\right)^{2} + t\left(0, 0, 1\right)^{2} \cdot t\left(1, 1, 0\right)^{2} + t\left(0, 1, 0\right)^{2} \cdot t\left(1, 0, 1\right)^{2} + t\left(1, 0, 0\right)^{2} \cdot t\left(0, 1, 1\right)^{2} - 2 \cdot \left(t\left(0, 0, 0\right) \cdot t\left(0, 0, 1\right) \cdot t\left(1, 1, 0\right) \cdot t\left(1, 1, 1\right) + t\left(0, 0, 0\right) \cdot t\left(0, 1, 0\right) \cdot t\left(1, 0, 1\right) \cdot t\left(1, 1, 1\right) + t\left(0, 0, 0\right) \cdot t\left(1, 0, 0\right) \cdot t\left(0, 1, 1\right) \cdot t\left(1, 1, 1\right) + t\left(0, 0, 1\right) \cdot t\left(0, 1, 0\right) \cdot t\left(1, 0, 1\right) \cdot t\left(1, 1, 0\right) + t\left(0, 0, 1\right) \cdot t\left(1, 0, 0\right) \cdot t\left(0, 1, 1\right) \cdot t\left(1, 1, 0\right) + t\left(0, 1, 0\right) \cdot t\left(1, 0, 0\right) \cdot t\left(0, 1, 1\right) \cdot t\left(1, 0, 1\right)\right) + 4 \cdot \left(t\left(0, 0, 0\right) \cdot t\left(0, 1, 1\right) \cdot t\left(1, 0, 1\right) \cdot t\left(1, 1, 0\right) + t\left(0, 0, 1\right) \cdot t\left(0, 1, 0\right) \cdot t\left(1, 0, 0\right) \cdot t\left(1, 1, 1\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.cayley` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The quartic has four square-product terms, six mixed terms with coefficient −2 and two mixed terms with coefficient 4.

**Definition 1.10 (The five J invariants).**

$$\forall psi \in CanonicalState,\; jInvariants\left(psi, 0\right) = \left|lambda1\left(psi\right) \cdot lambda4\left(psi\right) \cdot exp\left(phi\left(psi\right) \cdot i\right) - lambda2\left(psi\right) \cdot lambda3\left(psi\right)\right|^{2} \land \left(jInvariants\left(psi, 1\right) = lambda0\left(psi\right)^{2} \cdot lambda2\left(psi\right)^{2} \land \left(jInvariants\left(psi, 2\right) = lambda0\left(psi\right)^{2} \cdot lambda3\left(psi\right)^{2} \land \left(jInvariants\left(psi, 3\right) = lambda0\left(psi\right)^{2} \cdot lambda4\left(psi\right)^{2} \land jInvariants\left(psi, 4\right) = lambda0\left(psi\right)^{2} \cdot \left(\left|lambda1\left(psi\right) \cdot lambda4\left(psi\right) \cdot exp\left(phi\left(psi\right) \cdot i\right) - lambda2\left(psi\right) \cdot lambda3\left(psi\right)\right|^{2} + lambda2\left(psi\right)^{2} \cdot lambda3\left(psi\right)^{2} - lambda1\left(psi\right)^{2} \cdot lambda4\left(psi\right)^{2}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.jInvariants` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

Entry k is J_(k+1). These are the Acín invariants cited by the source: J₁ = |λ₁λ₄ exp(iφ) − λ₂λ₃|², J₂ = λ₀²λ₂², J₃ = λ₀²λ₃², J₄ = λ₀²λ₄² and J₅ = λ₀²(J₁ + λ₂²λ₃² − λ₁²λ₄²).

**Definition 1.11 (The GHZ-class condition).**

$$\forall psi \in CanonicalState,\; (isGHZ\left(psi\right)) \Leftrightarrow (lambda0\left(psi\right) \cdot lambda4\left(psi\right) \ne 0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isGHZ` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The GHZ class condition is λ₀ λ₄ ≠ 0.

**Definition 1.12 (The type-5 exclusion).**

$$\forall psi \in CanonicalState,\; (isType5\left(psi\right)) \Leftrightarrow (lambda0\left(psi\right) \ne 0 \land \left(lambda1\left(psi\right) \ne 0 \land \left(lambda2\left(psi\right) \ne 0 \land \left(lambda3\left(psi\right) \ne 0 \land \left(lambda4\left(psi\right) \ne 0 \land \left(\forall k \in Fin\left(5\right),\; jInvariants\left(psi, k\right) \ne 0\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isType5` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

Type 5 requires every λⱼ and every Jₖ to be nonzero. The witness has λ₁ = 0, so the full predicate excludes it without evaluating the J invariants.

**Definition 1.13 (Bloch-norm coordinates).**

$$\forall psi \in CanonicalState,\; blochLengths\left(psi\right) = (sqrt\left(\sum_{{i:Fin\left(3\right)}}(blochVectors\left(psi, 0, i\right)^{2})\right), sqrt\left(\sum_{{i:Fin\left(3\right)}}(blochVectors\left(psi, 1, i\right)^{2})\right), sqrt\left(\sum_{{i:Fin\left(3\right)}}(blochVectors\left(psi, 2, i\right)^{2})\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.blochLengths` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The three coordinates are the Euclidean lengths of the Bloch vectors obtained from the literal reduced density matrices. Each finite sum is the squared Euclidean norm.

**Definition 1.14 (Squared Bloch-vector norm).**

$$\forall rA \in \mathbb{R},\; \forall rB \in \mathbb{R},\; \forall rC \in \mathbb{R},\; normSquared\left((rA, rB, rC)\right) = rA^{2} + rB^{2} + rC^{2}$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.normSquared` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The squared norm of (r_A,r_B,r_C) is the sum of the three squared Bloch lengths.

**Definition 1.15 (The main diagonal line).**

$$V_{line}: Set\left(EuclideanSpace\left(\mathbb{R}, Fin\left(3\right)\right)\right) = Set.range\left((t: \mathbb{R}) \mapsto WithLp.toLp\left(2, ![t, t, t]\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.V_line` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The main diagonal is the range of t ↦ WithLp.toLp 2 ![t,t,t] in EuclideanSpace ℝ (Fin 3).

**Definition 1.16 (The Euclidean Bloch-length vector).**

$$\forall rA \in \mathbb{R},\; \forall rB \in \mathbb{R},\; \forall rC \in \mathbb{R},\; euclideanVector\left((rA, rB, rC)\right): EuclideanSpace\left(\mathbb{R}, Fin\left(3\right)\right) = WithLp.toLp\left(2, ![rA, rB, rC]\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.euclideanVector` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The real triple (r_A,r_B,r_C) is embedded as WithLp.toLp 2 ![r_A,r_B,r_C] in EuclideanSpace ℝ (Fin 3), which carries the Euclidean metric.

**Definition 1.17 (Distance to the main diagonal).**

$$\forall r \in Prod\left(\mathbb{R}, Prod\left(\mathbb{R}, \mathbb{R}\right)\right),\; distanceToDiagonal\left(r\right) = Metric.infDist\left(euclideanVector\left(r\right), V_{line}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.distanceToDiagonal` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The paper defines d(r⃗,V_line) as the Euclidean distance from r⃗ to the diagonal line. Metric.infDist takes the infimum of the Euclidean distances from euclideanVector(r) to points of V_line.

**Definition 1.18 (Canonical three-tangle).**

$$\forall psi \in CanonicalState,\; tangle\left(psi\right) = 4 \cdot \left|cayley\left(amplitudes\left(psi\right)\right)\right|$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.tangle` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The paper prints verbatim: “τ(ψ) = 4 |Hdet(t_ijk)| = 4 λ₀² λ₄².” (arXiv v2, p. 5, Eq. (10)). The definition uses the full Cayley quartic of the coefficient tensor. On this canonical family the quartic is λ₀²λ₄²; hence the three-tangle is 4λ₀²λ₄².

**Definition 1.19 (The Benedito–Sierra geometric ansatz).**

$$(claim) \Leftrightarrow (\exists F \in Prod\left(\mathbb{R}, Prod\left(\mathbb{R}, \mathbb{R}\right)\right) \to \mathbb{R},\; \left(\forall r \in Prod\left(\mathbb{R}, Prod\left(\mathbb{R}, \mathbb{R}\right)\right),\; 0 \le F\left(r\right)\right) \land \left(\forall psi \in CanonicalState,\; (isCanonical\left(psi\right)) \Rightarrow ((isGHZ\left(psi\right)) \Rightarrow ((\neg isType5\left(psi\right)) \Rightarrow (tangle\left(psi\right) = 1 - \frac{normSquared\left(blochLengths\left(psi\right)\right)}{3} - distanceToDiagonal\left(blochLengths\left(psi\right)\right) \cdot F\left(blochLengths\left(psi\right)\right))))\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.claim` (`✓ std3`).

*Citation.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

The paper states verbatim: “τ ( r⃗ ) = 1 − |r⃗|²/3 − d( r⃗, V_line ) · 𝓕(r⃗) where |ψ⟩ ∈ GHZ excluding type 5 and 𝓕(r⃗) ≥ 0.” (arXiv v2, p. 7, Eq. (15)). The formal encoding quantifies a nonnegative real function over all normalized canonical states in the GHZ class that are not type 5, with the one-qubit Bloch lengths and diagonal distance defined above.

**Theorem 1.20 (A type-4c diagonal counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* A. Benedito; G. Sierra (2025). *Visualizing Three-Qubit Entanglement*. URL: <https://arxiv.org/abs/2505.23638v2>.

*Commentary.*

For ψ = (|000⟩ + |101⟩ + |110⟩ + |111⟩)/2, the canonical parameters are (1/2,0,1/2,1/2,1/2;0). Its reduced states have Bloch lengths (1/2,1/2,1/2), so the distance to V_line is zero. The ansatz therefore gives 3/4, while τ = 4(1/2)²(1/2)² = 1/4. Hence no nonnegative F can satisfy the universal claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.CanonicalState`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.V_line`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.amplitudes`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.blochLengths`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.blochVectors`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.cayley`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.distanceToDiagonal`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.euclideanVector`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isCanonical`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isGHZ`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.isType5`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.jInvariants`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.jointDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.normSquared`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoA`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoB`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.rhoC`
- Truth anchor: `D5/S3/Quantum/Entanglement/ThreeQubitGeometricTangleRefutation.tangle`
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
