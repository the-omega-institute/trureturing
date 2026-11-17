# The odd-qubit Lorentz invariant range

## Abstract

For odd n, the Lorentz invariant of n-qubit states has exactly the real interval [-1/2,0] as its range.

All matrices have complex entries. The computational basis is the function type Fin n → Fin 2. A state is positive semidefinite with trace one. The Levi-Civita matrix is the displayed real two-by-two matrix, and epsN is its coordinatewise tensor power. The invariant is the trace in Eq. (54) of Cheng and Chen, arXiv:2605.19530v2, Definition 12 and Conjecture 24.

**Definition 1.1 (The two-dimensional Levi-Civita symbol).**

$$\operatorname{eps} = \begin{pmatrix}0&1\\-1&0\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.eps` (`✓ std3`).

*Citation.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

The matrix has rows and columns indexed by Fin 2 and entries 0, 1, -1, 0 in that order.

**Definition 1.2 (The tensor power).**

$$\forall (n: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\forall (j: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{epsN}\left(n, i, j\right) = \prod_{(k: \operatorname{Fin}\left(n\right))} (\operatorname{eps}\left(i\left(k\right), j\left(k\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.epsN` (`✓ std3`).

*Citation.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

For each natural n, epsN n has entry the finite product of eps at the corresponding bit coordinates.

**Definition 1.3 (An n-qubit state).**

$$\forall (n: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{IsState}\left(rho\right) = \left((\operatorname{Matrix.PosSemidef}\left(rho\right)) \land (\operatorname{Matrix.trace}\left(rho\right) = 1)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.IsState` (`✓ std3`).

*Citation.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

A matrix is a state exactly when it is positive semidefinite and has trace one.

**Definition 1.4 (The Lorentz invariant).**

$$\forall (n: \mathbb{N}), (\forall (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right)), (\operatorname{lorentz}\left(rho\right) = \operatorname{Matrix.trace}\left(\operatorname{Matrix.transpose}\left(rho\right)\cdot \operatorname{epsN}\left(n\right)\cdot rho\cdot \operatorname{epsN}\left(n\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.lorentz` (`✓ std3`).

*Citation.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

The invariant is Tr(rhoᵀ epsN n rho epsN n), the complex trace of the product in Eq. (54).

**Definition 1.5 (The range conjecture).**

$$\forall (n: \mathbb{N}), ((\operatorname{Odd}\left(n\right)) \Rightarrow (\{(z: \mathbb{C}) \mid (\exists (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{IsState}\left(rho\right)) \land (\operatorname{lorentz}\left(rho\right) = z)))\} = \operatorname{Set.image}\left(\lambda (x: \mathbb{R}) \mapsto ((x: \mathbb{C})), \operatorname{Set.Icc}\left(-\frac{1}{2}, 0\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.claim` (`✓ std3`).

*Citation.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

Conjecture 24 states verbatim: "Suppose ρ is an arbitrary n-qubit state with odd n, then the range of Lorentz invariant Iρ is [−1/2, 0]." (p. 12). The encoding takes the range as the set of complex values of lorentz on IsState matrices and the real interval as its complex image.

**Theorem 1.6 (The conjectured range is proved).**

$$\forall (n: \mathbb{N}), ((\operatorname{Odd}\left(n\right)) \Rightarrow (\{(z: \mathbb{C}) \mid (\exists (rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right), \mathbb{C}\right)), ((\operatorname{IsState}\left(rho\right)) \land (\operatorname{lorentz}\left(rho\right) = z)))\} = \operatorname{Set.image}\left(\lambda (x: \mathbb{R}) \mapsto ((x: \mathbb{C})), \operatorname{Set.Icc}\left(-\frac{1}{2}, 0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.result` (`✓ std3`). ∎

*Resolves.* `Problems/lorentzrange` (proved) by `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lorentzrange","declaration_gid":"D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Y. Cheng and L. Chen (2026). *Construction of three-qubit positive-partial-transpose entangled states of rank four*. URL: <https://arxiv.org/abs/2605.19530v2>.

*Commentary.*

For odd n, epsN is skew-symmetric, squares to minus the identity, and is unitary. The Breuer positive-map estimate applied to a state A and its spin-flip partner B gives 0 ≤ Re Tr(A B) ≤ 1/2. Cyclicity of trace identifies lorentz A with −Tr(A B), so every value lies in the stated interval.

The diagonal pair state p|0⋯0⟩⟨0⋯0|+(1−p)|1⋯1⟩⟨1⋯1| has invariant −2p(1−p). Choosing p=(1−sqrt(1+2x))/2 attains every x in [−1/2,0].

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.IsState`
- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.eps`
- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.epsN`
- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.lorentz`
- Truth anchor: `D5/S3/Quantum/Entanglement/Lorentz/ChengChenLorentzInvariantRange.result`
- Dependency: [D5/S3/Quantum/Tomography/PurityPythagorasDecomposition](../../Tomography/PurityPythagorasDecomposition.md)
