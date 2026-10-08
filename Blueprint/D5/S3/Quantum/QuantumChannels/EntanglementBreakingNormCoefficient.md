# Optimality of the coefficient in the entanglement-breaking norm inequality

## Abstract

For every dimension d ≥ 2, every Hermitian traceless basis λ₁, …, λ_{d²−1} with tr(λᵢλⱼ) = 2δᵢⱼ and every real B > d(d − 1)/2, some entanglement-breaking channel has Bloch data (A, c) with ‖A‖_*² + B|c|² > (d − 1)²; hence d(d − 1)/2 is the largest coefficient of |c|² for which the norm inequality for entanglement-breaking channels can hold.

**Definition 1.1 (Generalised Bloch bases).**

$$\forall d: \mathbb{N}, \forall \lambda: \operatorname{Fin}\left(d^{2} - 1\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsBlochBasis}\left(d, \lambda\right) \Leftrightarrow ((\forall i: \operatorname{Fin}\left(d^{2} - 1\right), \operatorname{IsHermitian}\left(\lambda(i)\right)) \land (\forall i: \operatorname{Fin}\left(d^{2} - 1\right), \operatorname{tr}\left(\lambda(i)\right) = 0) \land (\forall i, j: \operatorname{Fin}\left(d^{2} - 1\right), \operatorname{tr}\left(\lambda(i) \lambda(j)\right) = \operatorname{ite}\left(i = j, 2, 0\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.IsBlochBasis` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

A family λ of d² − 1 complex d × d matrices, indexed by Fin(d² − 1) with d² − 1 computed in the natural numbers, is a generalised Bloch basis when every member is Hermitian and traceless and tr(λᵢλⱼ) equals 2 for i = j and 0 otherwise; ite(p, x, y) denotes x when p holds and y otherwise. Together with the identity such a family spans the d × d matrices, and every density matrix is I/d + ½ Σᵢ rᵢλᵢ with real rᵢ = tr(λᵢρ). For d = 2 the Pauli matrices are an example and for general d the generalised Gell-Mann matrices.

**Definition 1.2 (Entanglement-breaking maps in Holevo form).**

$$\forall d: \mathbb{N}, \forall \phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsEntanglementBreaking}\left(\phi\right) \Leftrightarrow (\exists k: \mathbb{N}, \exists E, \sigma: \operatorname{Fin}\left(k\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsPOVM}\left(E\right) \land (\forall a: \operatorname{Fin}\left(k\right), \operatorname{PosSemidef}\left(\sigma(a)\right) \land \operatorname{tr}\left(\sigma(a)\right) = 1) \land (\forall X: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \phi(X) = \sum_{a:\operatorname{Fin}\left(k\right)} \operatorname{tr}\left(E(a) X\right) \sigma(a)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.IsEntanglementBreaking` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

A linear map φ on complex d × d matrices is entanglement breaking when it has a Holevo form φ(X) = Σ_a tr(E_a X) σ_a with finitely many positive semidefinite E_a summing to the identity and positive semidefinite σ_a of trace 1. MatrixMap is the frozen type of linear maps between matrix spaces of D5/S3/Quantum/Foundation/FiniteKrausChannel, and IsPOVM is the frozen predicate of D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation: every E_a is positive semidefinite and Σ_a E_a = I. A map of this form is completely positive and trace preserving, and (id ⊗ φ)(ρ) is separable for every state ρ.

**Definition 1.3 (The linear part of the Bloch representation).**

$$\forall d: \mathbb{N}, \forall \lambda: \operatorname{Fin}\left(d^{2} - 1\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall i, j: \operatorname{Fin}\left(d^{2} - 1\right), \operatorname{blochA}\left(\lambda, \phi\right)(i, j) = \frac{1}{2} \operatorname{re}\left(\operatorname{tr}\left(\lambda(i) \phi(\lambda(j))\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.blochA` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

The real (d² − 1) × (d² − 1) matrix A with A_{ij} = ½ Re tr(λᵢ φ(λⱼ)). For a generalised Bloch basis λ and a trace-preserving, Hermiticity-preserving φ, the Bloch vector r of a state, rᵢ = tr(λᵢρ), is sent to Ar + c, with c the translation part defined next.

**Definition 1.4 (The translation part of the Bloch representation).**

$$\forall d: \mathbb{N}, \forall \lambda: \operatorname{Fin}\left(d^{2} - 1\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall \phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall i: \operatorname{Fin}\left(d^{2} - 1\right), \operatorname{blochC}\left(\lambda, \phi\right)(i) = \operatorname{re}\left(\operatorname{tr}\left(\lambda(i) \phi(\frac{1}{\operatorname{cast}\left(d\right)} I)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.blochC` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

The real vector c with cᵢ = Re tr(λᵢ φ(I/d)), the Bloch vector of the image of the maximally mixed state; cast denotes the inclusion of the natural numbers in ℂ.

**Definition 1.5 (The coefficient cannot be increased).**

$$claim \Leftrightarrow (\forall d: \mathbb{N}, 2 \leq d \Rightarrow \forall \lambda: \operatorname{Fin}\left(d^{2} - 1\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsBlochBasis}\left(d, \lambda\right) \Rightarrow \forall B: \mathbb{R}, \frac{\operatorname{cast}\left(d\right) (\operatorname{cast}\left(d\right) - 1)}{2} < B \Rightarrow \exists \phi: \operatorname{MatrixMap}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{IsEntanglementBreaking}\left(\phi\right) \land (\operatorname{cast}\left(d\right) - 1)^{2} < \operatorname{traceNorm}\left(\operatorname{blochA}\left(\lambda, \phi\right)\right)^{2} + B \sum_{i:\operatorname{Fin}\left(d^{2} - 1\right)} (\operatorname{blochC}\left(\lambda, \phi\right)(i))^{2})$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.claim` (`✓ std3`).

*Citation.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

Theorem 1 of arXiv:2609.27906v1 states that the Bloch data (A, c) of an entanglement-breaking channel on d × d matrices satisfy ‖A‖_*² + (d(d − 1)/2)|c|² ≤ (d − 1)², with ‖A‖_* the trace norm and |c| the Euclidean norm, and item 3 of its open questions asks whether the coefficient d(d − 1)/2 is optimal. The inequality with a coefficient κ in place of d(d − 1)/2 becomes stronger as κ grows, so the coefficient is optimal exactly when no larger κ is admissible. The claim states this: for every d ≥ 2, every generalised Bloch basis and every real B > d(d − 1)/2 there is an entanglement-breaking φ with (d − 1)² < ‖A‖_*² + B|c|². Theorem 1 itself is not part of the statement. traceNorm is the frozen trace norm tr √(AᵀA) of D5/S3/Quantum/Foundation/FiniteTraceDistance; here cast denotes the inclusion of the natural numbers in ℝ.

**Theorem 1.6 (The coefficient d(d − 1)/2 is optimal).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* E. Kopel (2026). *A sharp norm inequality for entanglement-breaking channels*. DOI: [10.48550/arXiv.2609.27906](https://doi.org/10.48550/arXiv.2609.27906). URL: <https://arxiv.org/abs/2609.27906v1>.

*Commentary.*

Let P be the matrix unit E₀₀ and φ(X) = tr(X) P. φ has the Holevo form with the one-element measurement {I} and the state P. Every λⱼ is traceless, so φ(λⱼ) = 0 and A = 0, whose trace norm is 0. Since φ(I/d) = P, cᵢ = Re tr(λᵢP) = Re (λᵢ)₀₀, and (λᵢ)₀₀ is real because λᵢ is Hermitian. The d² matrices I/√d and λᵢ/√2 are orthonormal for the Hilbert–Schmidt inner product ⟨M, N⟩ = tr(M†N), hence an orthonormal basis of the d²-dimensional space of d × d matrices, and Parseval's identity for P gives 1 = tr(P†P) = 1/d + ½ Σᵢ (λᵢ)₀₀². Therefore |c|² = 2(d − 1)/d and ‖A‖_*² + B|c|² = 2(d − 1)B/d, which exceeds (d − 1)² exactly when B > d(d − 1)/2.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.IsBlochBasis`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.IsEntanglementBreaking`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.blochA`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.blochC`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/EntanglementBreakingNormCoefficient.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](ConcealmentKernelNecessityRefutation.md)
