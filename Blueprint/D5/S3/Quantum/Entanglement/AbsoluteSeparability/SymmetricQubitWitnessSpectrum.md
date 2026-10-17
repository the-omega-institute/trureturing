# Spectra of symmetric two-qubit witnesses

## Abstract

The spectra of symmetric two-qubit entanglement witnesses are characterized by two sharp inequalities on their three ordered eigenvalues.

**Definition 1.1 (Coherent vectors in Dicke coordinates).**

$$\forall (v:\operatorname{Fin}\left(2\right) \to \mathbb{C}), \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.coherent}\left(v\right) = ![v\left(0\right)^{2}, (\operatorname{Real.sqrt}\left(2\right):\mathbb{C}) \cdot v\left(0\right) \cdot v\left(1\right), v\left(1\right)^{2}]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.coherent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Champagne; Nathaniel Johnston; Mitchell MacDonald; Logan Pipes (2022). *Spectral properties of symmetric quantum states and symmetric entanglement witnesses*. DOI: [10.1016/j.laa.2022.05.004](https://doi.org/10.1016/j.laa.2022.05.004). URL: <https://arxiv.org/abs/2108.10405v1>.

*Commentary.*

In the orthonormal Dicke basis e00, (e01 + e10)/sqrt(2), e11 of the symmetric subspace of C2 tensor C2, the vector v tensor v has these three coordinates. The factor sqrt(2) comes from the normalization of the middle basis vector.

**Definition 1.2 (Nonnegative expectation on coherent vectors).**

$$\forall (W:\operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right)), (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.IsSymmetricWitness}\left(W\right)) \Leftrightarrow ((\operatorname{Matrix.IsHermitian}\left(W\right)) \land (\forall (v:\operatorname{Fin}\left(2\right) \to \mathbb{C}), 0 \le \operatorname{Complex.re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.coherent}\left(v\right)\right), \operatorname{Matrix.mulVec}\left(W, \operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.coherent}\left(v\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.IsSymmetricWitness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Champagne; Nathaniel Johnston; Mitchell MacDonald; Logan Pipes (2022). *Spectral properties of symmetric quantum states and symmetric entanglement witnesses*. DOI: [10.1016/j.laa.2022.05.004](https://doi.org/10.1016/j.laa.2022.05.004). URL: <https://arxiv.org/abs/2108.10405v1>.

*Commentary.*

A symmetric witness is a Hermitian operator on this three-dimensional space whose expectation on every coherent vector is nonnegative, as in Section 2.3. Hermiticity makes the expectation real, so taking its real part preserves the inequality.

**Definition 1.3 (The spectral characterization).**

$$(\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.claim}) \Leftrightarrow (\forall (\mu_{1}:\mathbb{R}), \forall (\mu_{2}:\mathbb{R}), \forall (\mu_{3}:\mathbb{R}), (\mu_{2} \le \mu_{1}) \Rightarrow ((\mu_{3} \le \mu_{2}) \Rightarrow ((\exists W \in \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right),\; (\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.IsSymmetricWitness}\left(W\right)) \land (\operatorname{Matrix.charpoly}\left(W\right) = (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((\mu_{1}:\mathbb{C})\right)) \cdot (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((\mu_{2}:\mathbb{C})\right)) \cdot (\operatorname{Polynomial.X} - \operatorname{Polynomial.C}\left((\mu_{3}:\mathbb{C})\right)))) \Leftrightarrow ((0 \le \mu_{2}) \land (-\operatorname{Real.sqrt}\left(\mu_{1} \cdot \mu_{2}\right) \le \mu_{3})))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.claim` (`✓ std3`).

*Citation.* Gabriel Champagne; Nathaniel Johnston; Mitchell MacDonald; Logan Pipes (2022). *Spectral properties of symmetric quantum states and symmetric entanglement witnesses*. DOI: [10.1016/j.laa.2022.05.004](https://doi.org/10.1016/j.laa.2022.05.004). URL: <https://arxiv.org/abs/2108.10405v1>.

*Commentary.*

The conjecture following Theorem 3 and in Section 6(c) asks whether mu2 >= 0 and mu3 >= -sqrt(mu1 mu2) characterize all symmetric witness spectra. Here eigenvalues mu1 >= mu2 >= mu3 mean that the characteristic polynomial is the displayed product over C, so multiplicities, repeated eigenvalues and zero eigenvalues are included. Positive semidefinite witnesses are included, as stipulated in footnote 1.

**Theorem 1.4 (The exact spectrum theorem).**

$$\operatorname{D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricQubitWitnessSpectrum.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/champagne-johnston-macdonald-pipes-2022-symmetric-witness-spectrum` (proved) by `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"champagne-johnston-macdonald-pipes-2022-symmetric-witness-spectrum","declaration_gid":"D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gabriel Champagne; Nathaniel Johnston; Mitchell MacDonald; Logan Pipes (2022). *Spectral properties of symmetric quantum states and symmetric entanglement witnesses*. DOI: [10.1016/j.laa.2022.05.004](https://doi.org/10.1016/j.laa.2022.05.004). URL: <https://arxiv.org/abs/2108.10405v1>.

*Commentary.*

The coherent vectors are exactly the null cone x^T ((0,0,-1),(0,1,0),(-1,0,0)) x = 0; explicitly the equation is x1^2 - 2 x0 x2 = 0. Diagonalizing the Hermitian matrix by a unitary U transports this cone to the eigenbasis: G = U^T ((0,0,-1),(0,1,0),(-1,0,0)) U is symmetric and unitary, and the quadratic expectation is diagonal there.

Suppose the third eigenvalue is -c with c > 0. Write A for the upper-left 2 by 2 submatrix (Gij) with i,j in {0,1}, and t = |G22|. Nonnegativity on the cone forces t > 0. For each u = (u0,u1), the two roots, counted with multiplicity, of G22 z^2 + 2(G02 u0 + G12 u1)z + u^T A u = 0 give c |u^T A u| <= t(mu1 |u0|^2 + mu2 |u1|^2).

The 2 by 2 bilinear determinant bound says that a complex symmetric matrix B satisfying |u^T B u| <= p |u0|^2 + q |u1|^2 for every u has p,q >= 0 and |det B| <= pq. Polarization bounds the bilinear form by the two corresponding quadratic weights. Applied to cA, this bound combines with the unitary submatrix identity |det A| = |G22| <= 1 to give mu1,mu2 >= 0 and c^2 <= t mu1 mu2 <= mu1 mu2. This yields the required lower bound for mu3; when mu3 >= 0 both inequalities follow directly from the ordering.

For sufficiency, the diagonal matrix diag(mu1,mu3,mu2) in the Dicke basis has the required characteristic polynomial. Its coherent expectation is (sqrt(mu1)|v0|^2 - sqrt(mu2)|v1|^2)^2 + 2(mu3 + sqrt(mu1 mu2))|v0|^2|v1|^2, which is nonnegative under the two spectral inequalities. This is the diagonal construction underlying the sufficient direction of Theorem 3.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.IsSymmetricWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.coherent`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricQubitWitnessSpectrum.result`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](../../Divergence/CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Zeros/PochhammerDeformation/QuadraticRadii](../../../Zeros/PochhammerDeformation/QuadraticRadii.md)
