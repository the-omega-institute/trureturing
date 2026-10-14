# The two-qubit SVD entanglement entropy lower bound

## Abstract

For two unit two-qubit states with nonzero reduced transition, SVD entanglement entropy is at least the smaller input entanglement entropy.

**Definition 1.1 (The reduced transition matrix).**

$$\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{Matrix.vecMulVec}\left(\operatorname{Function.uncurry}\left(A\right), \operatorname{star}\left(\operatorname{Function.uncurry}\left(B\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.reducedTransition` (`✓ std3`).

*Citation.* Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei (2023). *SVD entanglement entropy*. DOI: [10.1007/JHEP12(2023)123](https://doi.org/10.1007/JHEP12(2023)123). URL: <https://arxiv.org/abs/2307.06531v2>.

*Commentary.*

The coefficient matrices A and B represent the vectors psi and phi in the product basis. Matrix.vecMulVec forms the outer product of Function.uncurry A and star (Function.uncurry B). D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight traces out the second factor, giving the unnormalized reduced transition Tr_B |psi><phi| of Section 2.

**Definition 1.2 (The reduced density matrix).**

$$\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedDensity}\left(A\right) = \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling}\left(A\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.reducedDensity` (`✓ std3`).

*Citation.* Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei (2023). *SVD entanglement entropy*. DOI: [10.1007/JHEP12(2023)123](https://doi.org/10.1007/JHEP12(2023)123). URL: <https://arxiv.org/abs/2307.06531v2>.

*Commentary.*

D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling A is the outer product |psi><psi|. Its right partial trace is the first subsystem's reduced matrix. When RHLinalg.frobSq A = 1, this matrix is positive semidefinite with trace one.

**Definition 1.3 (The normalized absolute value of a transition).**

$$\forall T \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.svdDensity}\left(T\right) = \operatorname{SMul.smul}\left((\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{CFC.sqrt}\left(\operatorname{Matrix.conjTranspose}\left(T\right) \cdot T\right)\right)\right))^{-1}, \operatorname{CFC.sqrt}\left(\operatorname{Matrix.conjTranspose}\left(T\right) \cdot T\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.svdDensity` (`✓ std3`).

*Citation.* Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei (2023). *SVD entanglement entropy*. DOI: [10.1007/JHEP12(2023)123](https://doi.org/10.1007/JHEP12(2023)123). URL: <https://arxiv.org/abs/2307.06531v2>.

*Commentary.*

Equation (2.1) normalizes the positive square root of T conjugate-transpose times T by its trace. CFC.sqrt is the positive matrix square root; its trace is real. SMul.smul denotes multiplication of the matrix by the real scalar shown. For nonzero T the trace is positive, so the resulting matrix is positive semidefinite with trace one. The formula is defined for every T; at zero it gives the zero matrix.

**Definition 1.4 (The lower bound for arbitrary two-qubit inputs).**

$$(\operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.claim}) \Leftrightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right),\; (\operatorname{RHLinalg.frobSq}\left(A\right) = 1) \Rightarrow ((\operatorname{RHLinalg.frobSq}\left(B\right) = 1) \Rightarrow ((\operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right) \ne 0) \Rightarrow (\operatorname{min}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy}\left((\operatorname{Matrix.PosSemidef.isHermitian}\left((\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_{posSemidef}}\left((\operatorname{D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling_{psd}}\left(A\right))\right))\right))\right), \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy}\left((\operatorname{Matrix.PosSemidef.isHermitian}\left((\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight_{posSemidef}}\left((\operatorname{D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings.pureCoupling_{psd}}\left(B\right))\right))\right))\right)\right) \le \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy}\left((\operatorname{Matrix.PosSemidef.isHermitian}\left((\operatorname{Matrix.PosSemidef.smul}\left((\operatorname{Matrix.nonneg_{iff_{posSemidef}}.mp}\left((\operatorname{CFC.sqrt_{nonneg}}\left((\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right)\right) \cdot \operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right))\right))\right)), (\operatorname{inv_{nonneg}.mpr}\left(((\operatorname{Complex.nonneg_{iff}.mp}\left((\operatorname{Matrix.PosSemidef.trace_{nonneg}}\left((\operatorname{Matrix.nonneg_{iff_{posSemidef}}.mp}\left((\operatorname{CFC.sqrt_{nonneg}}\left((\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right)\right) \cdot \operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.reducedTransition}\left(A, B\right))\right))\right))\right))\right)).1)\right))\right))\right))\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.claim` (`✓ std3`).

*Citation.* Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei (2023). *SVD entanglement entropy*. DOI: [10.1007/JHEP12(2023)123](https://doi.org/10.1007/JHEP12(2023)123). URL: <https://arxiv.org/abs/2307.06531v2>.

*Commentary.*

Coefficient matrices of Frobenius norm one are exactly the unit vectors of the tensor product of two copies of the two-dimensional complex Hilbert space. Section 3.3 and Equation (3.38) propose the lower bound by the smaller input entanglement entropy, without requiring the two input entropies to coincide. The source's factor 1/<phi|psi> cancels in the SVD density matrix, so the nonzero reduced-transition condition also allows orthogonal input vectors. By definition, the three matrices underlying the entropy proof arguments are reducedDensity A, reducedDensity B and svdDensity (reducedTransition A B). D5.S3.Quantum.Information.PartialTraceMutualInformation.spectralEntropy uses natural logarithms and includes zero eigenvalues with zero contribution.

**Theorem 1.5 (SVD entropy dominates the smaller input entropy).**

$$\operatorname{D5.S3.Quantum.Information.TwoQubitSVDEntropyLowerBound.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/parzygnat-takayanagi-taki-wei-2023-two-qubit-svd-entropy-lower-bound` (proved) by `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"parzygnat-takayanagi-taki-wei-2023-two-qubit-svd-entropy-lower-bound","declaration_gid":"D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Arthur J. Parzygnat, Tadashi Takayanagi, Yusuke Taki, Zixia Wei (2023). *SVD entanglement entropy*. DOI: [10.1007/JHEP12(2023)123](https://doi.org/10.1007/JHEP12(2023)123). URL: <https://arxiv.org/abs/2307.06531v2>.

*Commentary.*

The partial trace gives T = A B conjugate-transpose and the reduced input matrices rho_psi = A A conjugate-transpose and rho_phi = B B conjugate-transpose. The two-by-two adjugate identity is ||A B conjugate-transpose||_F^2 + ||A adj(B)||_F^2 = ||A||_F^2 ||B||_F^2. Applying ||C||_F^2 >= 2 |det C| to C = A adj(B), and using det adj(B) = det B, yields ||A B conjugate-transpose||_F^2 + 2 |det A| |det B| <= 1 for the unit inputs.

Set D = CFC.sqrt (T conjugate-transpose times T) and s = Tr D. Then det D = |det T| and s^2 = ||T||_F^2 + 2 |det T| <= 1. Since T is nonzero, s is positive. Thus Q = D/s is a density matrix and det Q = |det A| |det B|/s^2 >= |det A| |det B| >= min(|det A|^2, |det B|^2). The last two squares are det rho_psi and det rho_phi.

A two-by-two density matrix has eigenvalues p and 1 - p, with p between one half and one. Its determinant is p(1 - p) and its spectral entropy is Real.binEntropy p. This entropy increases with the determinant. The determinant comparison therefore gives the asserted entropy lower bound, including singular input states. This proves the two-qubit inequality proposed in Section 3.3 and Equation (3.38).

## References

- Truth anchor: `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.reducedDensity`
- Truth anchor: `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.reducedTransition`
- Truth anchor: `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.result`
- Truth anchor: `D5/S3/Quantum/Information/TwoQubitSVDEntropyLowerBound.svdDensity`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/Entanglement/GraphDensity/FormationBounds](../Entanglement/GraphDensity/FormationBounds.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QubitWassersteinCouplings](../QuantumChannels/QubitWassersteinCouplings.md)
