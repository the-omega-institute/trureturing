# Gaussian atemporality implies entanglement

## Abstract

Positive partial transpose implies temporal compatibility in both directions for physical two-mode Gaussian covariance matrices; Gaussian atemporality therefore implies entanglement in the covariance PPT formulation.

**Definition 1.1 (Space-time covariance matrix).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \operatorname{covariance}\left(VA, VB, C\right) = (\operatorname{Matrix.fromBlocks}\left(VA, C, \operatorname{Matrix.transpose}\left(C\right), VB\right))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.covariance` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Equation (2), p. 3, is V_AB = [[V_A,C],[Cᵀ,V_B]]. The Sum index lists Alice's two quadratures before Bob's two quadratures.

**Definition 1.2 (Locally diagonal covariance matrices).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsStandardForm}\left(VA, VB\right)) \Leftrightarrow ((\operatorname{Matrix.IsDiag}\left(VA\right)) \land (\operatorname{Matrix.IsDiag}\left(VB\right)))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsStandardForm` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Definition 1, p. 3: "Let Alice and Bob each have access to a qumode with standard basis (q̂_A,p̂_A) and (q̂_B,p̂_B), with locally diagonal covariance matrices V_A and V_B." VA and VB are real matrices indexed by Fin 2; Matrix.IsDiag expresses locally diagonal covariance matrices.

**Definition 1.3 (The spatial uncertainty inequality).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsSpatiallyPhysical}\left(VA, VB, C\right)) \Leftrightarrow (\operatorname{Matrix.PosSemidef}\left((\operatorname{Matrix.map}\left(\operatorname{covariance}\left(VA, VB, C\right), \operatorname{Complex.ofReal}\right) + \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{Matrix.map}\left(\operatorname{Matrix.fromBlocks}\left(\operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2}, 0, 0, \operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2}\right), \operatorname{Complex.ofReal}\right)\right))\right))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsSpatiallyPhysical` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

The real covariance matrix obeys the uncertainty principle V_AB + i(Ω ⊕ Ω) ≥ 0, with ℏ = 2. Matrix.PosSemidef includes Hermiticity.

**Definition 1.4 (Forward atemporality matrix).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \operatorname{forwardX}\left(VA, VB, C\right) = (\operatorname{let} T:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right):=(\operatorname{Matrix.transpose}\left(C\right) \cdot \operatorname{Inv.inv}\left(VA\right)); \operatorname{let} N:\operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right):=(VB - \operatorname{Matrix.transpose}\left(C\right) \cdot \operatorname{Inv.inv}\left(VA\right) \cdot C); \operatorname{Matrix.map}\left(N, \operatorname{Complex.ofReal}\right) + \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{Matrix.map}\left(\operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2}, \operatorname{Complex.ofReal}\right)\right) - \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{Matrix.map}\left(T \cdot \operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2} \cdot \operatorname{Matrix.transpose}\left(T\right), \operatorname{Complex.ofReal}\right)\right))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.forwardX` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Equations (7) and (8), p. 4: T = Cᵀ V_A⁻¹, N = V_B − Cᵀ V_A⁻¹ C and X(T,N) ≡ N + iΩ − iTΩTᵀ. Inv.inv uses the total nonsingular matrix inverse; physicality ensures that the local blocks are invertible.

**Definition 1.5 (Incompatibility in both directions).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsGaussianAtemporal}\left(VA, VB, C\right)) \Leftrightarrow ((\neg \operatorname{Matrix.PosSemidef}\left((\operatorname{forwardX}\left(VA, VB, C\right))\right)) \land (\neg \operatorname{Matrix.PosSemidef}\left((\operatorname{forwardX}\left(VB, VA, \operatorname{Matrix.transpose}\left(C\right)\right))\right)))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsGaussianAtemporal` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Section III.B, p. 4: "We then say that V_AB is Gaussian atemporal if it is Gaussian-atemporal in both temporal direction." The two negated Matrix.PosSemidef predicates express failure of the two channel complete-positivity inequalities.

**Definition 1.6 (Partial transpose on Alice).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \operatorname{partialTransposeA}\left(VA, VB, C\right) = (\operatorname{let} Lambda:\operatorname{Matrix}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Sum}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \mathbb{R}\right):=(\operatorname{Matrix.fromBlocks}\left(\operatorname{Matrix.diagonal}\left(![1,-1]\right), 0, 0, 1\right)); Lambda \cdot \operatorname{covariance}\left(VA, VB, C\right) \cdot Lambda)$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.partialTransposeA` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Partial transposition on Alice flips p_A. In the real covariance matrix it acts by Λ V_AB Λ, with Λ = diag(1,−1,1,1); Matrix.diagonal ![1,−1] is Alice's momentum flip.

**Definition 1.7 (The two-mode Gaussian PPT entanglement test).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsEntangled}\left(VA, VB, C\right)) \Leftrightarrow (\neg \operatorname{Matrix.PosSemidef}\left((\operatorname{Matrix.map}\left(\operatorname{partialTransposeA}\left(VA, VB, C\right), \operatorname{Complex.ofReal}\right) + \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{Matrix.map}\left(\operatorname{Matrix.fromBlocks}\left(\operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2}, 0, 0, \operatorname{D5.S3.Quantum.Thermal.PositiveOneModeWilliamson.physicalJ2}\right), \operatorname{Complex.ofReal}\right)\right))\right))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsEntangled` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Section III.D, p. 5, uses the positive partial transpose criterion. This predicate is failure of the partially transposed uncertainty inequality. Its interpretation as entanglement uses the source's two-mode Gaussian PPT criterion; a Hilbert-space separability theorem is outside the matrix statement.

**Definition 1.8 (The entanglement assertion).**

$$(claim) \Leftrightarrow (\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsStandardForm}\left(VA, VB\right)) \Rightarrow ((\operatorname{IsSpatiallyPhysical}\left(VA, VB, C\right)) \Rightarrow ((\operatorname{IsGaussianAtemporal}\left(VA, VB, C\right)) \Rightarrow (\operatorname{IsEntangled}\left(VA, VB, C\right)))))$$

*Formalization.* `D5/S3/Estimation/GaussianAtemporalityEntanglement.claim` (`✓ std3`).

*Citation.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

Section III.D, p. 6: "From Fig. 3, Gaussian-atemporality appears to imply entanglement. The converse, on the other hand is not generally true." The quantifiers range over all real two-by-two local blocks VA, VB and cross block C, in quadrature order (q_A,p_A,q_B,p_B), with ℏ = 2. Standard form means locally diagonal blocks. IsSpatiallyPhysical is the uncertainty inequality; IsGaussianAtemporal requires incompatibility in both directions; IsEntangled is failure of the partially transposed uncertainty inequality, the two-mode Gaussian PPT test used by the source.

**Theorem 1.9 (Gaussian atemporality implies entanglement).**

$$\forall VA \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall VB \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; \forall C \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{R}\right),\; (\operatorname{IsStandardForm}\left(VA, VB\right)) \Rightarrow ((\operatorname{IsSpatiallyPhysical}\left(VA, VB, C\right)) \Rightarrow ((\operatorname{IsGaussianAtemporal}\left(VA, VB, C\right)) \Rightarrow (\operatorname{IsEntangled}\left(VA, VB, C\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/GaussianAtemporalityEntanglement.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Minjeong Song; Jayne Thompson; Matthew S. Winnel; Biveen Shajilal; Timothy C. Ralph; Syed M. Assad; Mile Gu (2025). *Gaussian Atemporality: When Gaussian Quantum Correlations Imply Common Cause*. DOI: [10.48550/arXiv.2508.11804](https://doi.org/10.48550/arXiv.2508.11804). URL: <https://arxiv.org/abs/2508.11804v2>.

*Commentary.*

A physical local uncertainty matrix has strictly positive real covariance: a null quadratic form would annihilate its vector, whose imaginary part then forces Ωx = 0. Thus both local blocks are invertible. Conjugating the PPT inequality by the momentum flip gives H = V_AB + i((−Ω) ⊕ Ω) positive semidefinite. With T = Cᵀ VA⁻¹ and K = [−T,1], matrix multiplication gives K V_AB Kᵀ = N and K((−Ω) ⊕ Ω)Kᵀ = Ω − TΩTᵀ. Congruence yields forwardX positive semidefinite. Complex conjugation and exchange of Alice and Bob give the reverse direction. Either directional incompatibility therefore contradicts PPT. Diagonality of the local blocks is unnecessary for this argument.

## References

- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsEntangled`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsGaussianAtemporal`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsSpatiallyPhysical`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.IsStandardForm`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.claim`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.covariance`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.forwardX`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.partialTransposeA`
- Truth anchor: `D5/S3/Estimation/GaussianAtemporalityEntanglement.result`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../Quantum/FiniteDimensional.md)
- Dependency: [D5/S3/Quantum/Thermal/PositiveOneModeWilliamson](../Quantum/Thermal/PositiveOneModeWilliamson.md)
