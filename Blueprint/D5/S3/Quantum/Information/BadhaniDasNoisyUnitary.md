# Conditional min-entropy of noisy unitaries

## Abstract

White-noise mixtures of arbitrary bipartite unitaries with qubit conditioning attain the Choi-state upper bound on conditional min-entropy.

**Definition 1.1 (Max-relative entropy).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall rho \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall sigma \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \operatorname{Dmax}\left(rho, sigma\right) = \operatorname{ite}\left((\exists t \in \mathbb{R},\; (0 \le t) \land (rho \le (t) \cdot (sigma))), (\operatorname{Real.logb}\left(2, \operatorname{sInf}\left(\{(t: \mathbb{R}) \mid (0 \le t) \land (rho \le (t) \cdot (sigma))\}\right)\right): \operatorname{EReal}), \operatorname{Top.top}\right)$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.Dmax` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section II.2, page 10: “D_max(ρ‖σ) = log inf{λ ≥ 0 : ρ ≤ λσ}”, “where D_max(ρ‖σ) = +∞ if supp(ρ) ⊄ supp(σ).” The carrier n is finite. MatrixOrder is the Loewner order; real scalar multiplication and base-two logarithms are used. The value is in EReal, and the empty feasible set gives top.

**Definition 1.2 (Conditional min-entropy of a state).**

$$\forall X \in \operatorname{Type},\; [\operatorname{Fintype}\left(X\right)] [\operatorname{DecidableEq}\left(X\right)] \forall Y \in \operatorname{Type},\; [\operatorname{Fintype}\left(Y\right)] [\operatorname{DecidableEq}\left(Y\right)] \forall rho \in \operatorname{Matrix}\left((X \times Y), (X \times Y), \mathbb{C}\right),\; \operatorname{condMinEntropy}\left(rho\right) = -\operatorname{iInf}\left(\operatorname{fun} (sigma: \operatorname{DensityState}\left(Y\right)) \mapsto \operatorname{Dmax}\left(rho, \operatorname{Matrix.kroneckerMap}\left(\operatorname{fun} a b \mapsto a*b, (1: \operatorname{Matrix}\left(X, X, \mathbb{C}\right)), \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(sigma\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.condMinEntropy` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Table I, page 11: “S_∞(A|B)_ρ := −inf_{σ∈St(B)} D_∞(ρ_{AB}‖1_A ⊗ σ_B).” DensityState Y is St(B); CStarMatrix.ofMatrix.symm converts its value to matrix coordinates. The two finite factors are X and Y.

**Definition 1.3 (The bipartite Choi operator).**

$$\forall d \in \mathbb{N},\; \forall N \in (\operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)),\; \operatorname{choiN}\left(N\right) = \operatorname{fun} (x: ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto \operatorname{fun} (y: ((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)) \times (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)))) \mapsto N\left(\operatorname{Matrix.single}\left((x.1.1, x.2.1), (y.1.1, y.2.1), (1: \mathbb{C})\right), (x.1.2, x.2.2), (y.1.2, y.2.2)\right)$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.choiN` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section V, page 18: “The Choi operator Γ^N of a bipartite channel N_{A′B′→AB} is Γ^N_{R_AAR_BB} = N(Γ_{R_AA′} ⊗ Γ_{R_BB′}), where Γ_{R_AA′} denotes a maximally entangled operator.” The matrix units implement this expression. The factors are ordered (R_A, A), (R_B, B), with A′ = A = Fin d and B′ = B = Fin 2.

**Definition 1.4 (The normalized Choi state).**

$$\forall d \in \mathbb{N},\; \forall N \in (\operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)),\; \operatorname{choiState}\left(N\right) = ((((d) * (2): \mathbb{N}): \mathbb{R})^{-1}) \cdot (\operatorname{choiN}\left(N\right))$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.choiState` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section II, page 8: “The Choi state of a bipartite quantum channel N_{A′B′→AB} is Φ^N_{R_AAR_BB} = N(Φ_{R_AA′} ⊗ Φ_{R_BB′}).” The normalization is the inverse of the input dimension 2d. The expression is defined for every matrix map, and is a normalized state on the noisy-unitary maps in the theorem.

**Definition 1.5 (Conditional min-entropy of a channel).**

$$\forall d \in \mathbb{N},\; \forall N \in (\operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right) \to \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)),\; \operatorname{channelCondMinEntropy}\left(N\right) = -\operatorname{iInf}\left(\operatorname{fun} (Q: \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)) \mapsto \operatorname{Dmax}\left(\operatorname{choiN}\left(N\right), \operatorname{Matrix.kroneckerMap}\left(\operatorname{fun} a b \mapsto a*b, (1: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), \operatorname{fun} (x: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto \operatorname{fun} (y: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto \operatorname{CStarMatrix.ofMatrix.symm}\left(Q.toCompletelyPositiveMap\left(\operatorname{CStarMatrix.ofMatrix}\left(\operatorname{Matrix.single}\left(x.1, y.1, (1: \mathbb{C})\right)\right)\right), x.2, y.2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.channelCondMinEntropy` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section V, page 18 gives “S_∞[A|B]_N := −inf_{Q∈Ch(B′,B)} D_∞[N_{A′B′→AB}‖R^1_{A′→A} ⊗ Q_{B′→B}]” and its equal Choi-operator expression “−inf_{Q∈Ch(B′,B)} D_∞(Γ^N_{R_AAR_BB}‖1_{R_AA} ⊗ Γ^Q_{R_BB})”. This definition uses that second expression, with QuantumChannel (Fin 2) (Fin 2) and the full matrix-unit expression for Γ^Q.

**Definition 1.6 (A unitary mixed with white noise).**

$$\forall d \in \mathbb{N},\; \forall U \in \operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall p \in \mathbb{R},\; \forall Z \in \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \operatorname{noisyUnitary}\left(U, p, Z\right) = (p) \cdot ((\operatorname{Matrix.trace}\left(Z\right)) \cdot (((((d) * (2): \mathbb{N}): \mathbb{C})^{-1}) \cdot ((1: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right))))) + (1-p) \cdot ((((U: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right))) * (Z)) * (\operatorname{star}\left((U: \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.noisyUnitary` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section VI.1, page 31: “let N_p := pR^π + (1 − p)U for p ∈ [0, 1]”. Here R^π(Z) = tr(Z)1/(2d) and U(Z) = U Z U†. The definition allows every real p; the theorem restricts p to the stated interval.

**Definition 1.7 (The Badhani–Das conjecture with qubit conditioning).**

$$\operatorname{claim} = (\forall d \in \mathbb{N},\; (1 \le d) \Rightarrow (\forall U \in \operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall p \in \mathbb{R},\; (0 \le p) \Rightarrow ((p \le 1) \Rightarrow (\operatorname{channelCondMinEntropy}\left(\operatorname{noisyUnitary}\left(U, p\right)\right) = \operatorname{condMinEntropy}\left(\operatorname{choiState}\left(\operatorname{noisyUnitary}\left(U, p\right)\right)\right) - (\operatorname{Real.logb}\left(2, (d: \mathbb{R})\right): \operatorname{EReal})))))$$

*Formalization.* `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.claim` (`✓ std3`).

*Citation.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

Section VI.1, page 31: “We conjecture that Proposition 10 can be extended to all unitaries with added white noise. We leave this as an open problem.” Proposition 10 says: “For an arbitrary unitary channel U_{A′B′→AB} such that |B′| = |B| = 2, we have S_∞[A|B]_U = S_∞(R_AA|R_BB)_{Φ^U} − log|A′|.” The dimension d ranges over all positive naturals, the unitary acts on Fin d × Fin 2, and p ranges over [0, 1]. No choice of unitary or bound on d is imposed.

**Theorem 1.8 (White noise preserves equality with the Choi-state bound).**

$$\forall d \in \mathbb{N},\; (1 \le d) \Rightarrow (\forall U \in \operatorname{Matrix.unitaryGroup}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right),\; \forall p \in \mathbb{R},\; (0 \le p) \Rightarrow ((p \le 1) \Rightarrow (\operatorname{channelCondMinEntropy}\left(\operatorname{noisyUnitary}\left(U, p\right)\right) = \operatorname{condMinEntropy}\left(\operatorname{choiState}\left(\operatorname{noisyUnitary}\left(U, p\right)\right)\right) - (\operatorname{Real.logb}\left(2, (d: \mathbb{R})\right): \operatorname{EReal}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Badhani and S. Das (2026). *Conditional channel entropy sets fundamental limits on thermodynamic quantum information processing*. DOI: [10.48550/arXiv.2604.01217](https://doi.org/10.48550/arXiv.2604.01217). URL: <https://arxiv.org/abs/2604.01217v2>.

*Commentary.*

The reduced two-qubit Choi matrix has both marginals maximally mixed. In the magic basis it is real symmetric, so its real orthonormal eigenvectors give a maximally entangled eigenbasis. Signs in this eigenbasis have unitary partners on the other factor. Their tensor products fix the pure Choi vector and the white-noise matrix. Averaging a feasible optimizer over these signs preserves its trace and makes it the normalized Choi matrix of a channel. The state and channel optimizations therefore have equal costs after scaling by d, which subtracts log₂ d from the entropy. The proof includes singular eigenvalues, the endpoints p = 0 and p = 1, and d = 1. Conditioning dimensions greater than two are outside this statement.

## References

- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.Dmax`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.channelCondMinEntropy`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.choiN`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.choiState`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.claim`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.condMinEntropy`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.noisyUnitary`
- Truth anchor: `D5/S3/Quantum/Information/BadhaniDasNoisyUnitary.result`
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Algebra/GramUnitaryExtension](../Algebra/GramUnitaryExtension.md)
- Dependency: [D5/S3/Quantum/Recovery/LiJiangPolarPairOptimalityRefutation](../Recovery/LiJiangPolarPairOptimalityRefutation.md)
