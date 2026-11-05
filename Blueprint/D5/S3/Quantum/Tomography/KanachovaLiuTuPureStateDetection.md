# Kanachova–Liu–Tu pure-state detection

## Abstract

The fixed qubit-qutrit reconstruction has a negative real eigenvalue for every normalized entangled pure state.

**Definition 1.1 (The fixed local matrix).**

$$U = (!![0,0,-1;0,1,0;-1,0,0]: Matrix\left(Fin\left(3\right), Fin\left(3\right), \mathbb{C}\right))$$

*Formalization.* `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.U` (`✓ std3`).

*Citation.* Veronica Kanachova; Feng Liu; Zhoudunming Tu (2026). *Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems*. DOI: [10.48550/arXiv.2609.11151](https://doi.org/10.48550/arXiv.2609.11151). URL: <https://arxiv.org/abs/2609.11151v1>.

*Commentary.*

Equation (S18) in the ordered basis +1, 0, -1.

**Definition 1.2 (The local unitary conjugation).**

$$\forall (rho: Matrix\left((Fin\left(2\right)\times Fin\left(3\right)), (Fin\left(2\right)\times Fin\left(3\right)), \mathbb{C}\right)), localConjugation\left(rho\right) = \operatorname{let} K:= \operatorname{Matrix.kronecker}\left((1: Matrix\left(Fin\left(2\right), Fin\left(2\right), \mathbb{C}\right)), U\right); K \cdot rho \cdot \operatorname{Matrix.conjTranspose}\left(K\right)$$

*Formalization.* `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.localConjugation` (`✓ std3`).

*Citation.* Veronica Kanachova; Feng Liu; Zhoudunming Tu (2026). *Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems*. DOI: [10.48550/arXiv.2609.11151](https://doi.org/10.48550/arXiv.2609.11151). URL: <https://arxiv.org/abs/2609.11151v1>.

*Commentary.*

Equation (S19): conjugation by the tensor product of the qubit identity and U.

**Definition 1.3 (The measured reconstruction).**

$$\forall (rho: Matrix\left((Fin\left(2\right)\times Fin\left(3\right)), (Fin\left(2\right)\times Fin\left(3\right)), \mathbb{C}\right)), measured\left(rho\right) = \operatorname{SMul.smul}\left((\frac{1}{2}: \mathbb{C}), rho + localConjugation\left(partialTranspose\left(rho\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.measured` (`✓ std3`).

*Citation.* Veronica Kanachova; Feng Liu; Zhoudunming Tu (2026). *Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems*. DOI: [10.48550/arXiv.2609.11151](https://doi.org/10.48550/arXiv.2609.11151). URL: <https://arxiv.org/abs/2609.11151v1>.

*Commentary.*

Equation (3), p. 2, with Eqs. (S18)–(S19), p. 9: the reconstruction is the average of the input and its second-factor partial transpose conjugated by the fixed local matrix. The source says: “Let $\rho_{\mathrm{meas}}$ denote the density matrix obtained by setting the 23 measured parameters to their observed values and the inaccessible 12 to zero, which is the most complete reconstruction available from the decay angular distributions alone.” The first coordinate is the qubit; qutrit indices 0, 1, 2 correspond to +1, 0, −1. The displayed literal matrix is U of Eq. (S18). Matrix.kronecker and Matrix.conjTranspose have their usual complex-matrix meanings; partialTranspose is the second-factor transpose from AbsolutePPT.Bipartite.

**Definition 1.4 (The pure-state detection conjecture).**

$$\forall (psi: (Fin\left(2\right)\times Fin\left(3\right)) \to \mathbb{C}), (dotProduct\left(star\left(psi\right), psi\right) = 1) \Rightarrow ((\neg (\exists (a: Fin\left(2\right) \to \mathbb{C}), \exists (b: Fin\left(3\right) \to \mathbb{C}), \forall (i: Fin\left(2\right)), \forall (j: Fin\left(3\right)), psi\left((i,j)\right) = a\left(i\right) \cdot b\left(j\right))) \Rightarrow (\exists (eigenvalue: \mathbb{R}), \exists (w: (Fin\left(2\right)\times Fin\left(3\right)) \to \mathbb{C}), (eigenvalue<0) \land ((w \ne 0) \land (\operatorname{Matrix.mulVec}\left(measured\left(rankOneDensity\left(psi\right)\right), w\right) = \operatorname{SMul.smul}\left((eigenvalue: \mathbb{C}), w\right)))))$$

*Formalization.* `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.claim` (`✓ std3`).

*Citation.* Veronica Kanachova; Feng Liu; Zhoudunming Tu (2026). *Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems*. DOI: [10.48550/arXiv.2609.11151](https://doi.org/10.48550/arXiv.2609.11151). URL: <https://arxiv.org/abs/2609.11151v1>.

*Commentary.*

Appendix §.7, p. 9, immediately after Proposition 1, verbatim: “We therefore *conjecture*, without proof, that $\rho_{\mathrm{meas}}$ detects every pure entangled state of this system.” The amplitude vector psi ranges over all six complex coordinates. Its squared norm is one, and it has no product factorization into a two-coordinate vector and a three-coordinate vector. Detection means that measured(rankOneDensity psi) has a strictly negative real eigenvalue with a nonzero complex eigenvector. rankOneDensity is the existing PureStateHandshake construction Matrix.vecMulVec psi (star psi). No Schmidt basis is fixed.

**Theorem 1.5 (Every entangled pure state is detected).**

$$\forall (psi: (Fin\left(2\right)\times Fin\left(3\right)) \to \mathbb{C}), (dotProduct\left(star\left(psi\right), psi\right) = 1) \Rightarrow ((\neg (\exists (a: Fin\left(2\right) \to \mathbb{C}), \exists (b: Fin\left(3\right) \to \mathbb{C}), \forall (i: Fin\left(2\right)), \forall (j: Fin\left(3\right)), psi\left((i,j)\right) = a\left(i\right) \cdot b\left(j\right))) \Rightarrow (\exists (eigenvalue: \mathbb{R}), \exists (w: (Fin\left(2\right)\times Fin\left(3\right)) \to \mathbb{C}), (eigenvalue<0) \land ((w \ne 0) \land (\operatorname{Matrix.mulVec}\left(measured\left(rankOneDensity\left(psi\right)\right), w\right) = \operatorname{SMul.smul}\left((eigenvalue: \mathbb{C}), w\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Veronica Kanachova; Feng Liu; Zhoudunming Tu (2026). *Qubit–Qutrit Quantum Tomography of hadronic Λφ and ΛK*0 systems*. DOI: [10.48550/arXiv.2609.11151](https://doi.org/10.48550/arXiv.2609.11151). URL: <https://arxiv.org/abs/2609.11151v1>.

*Commentary.*

Writing the two rows of psi as u and v, the vector (U conjugate(v), −U conjugate(u)) has expectation equal to minus the sum of the squared absolute values of the three two-by-two minors. A non-product input has a nonzero minor, so this expectation is strictly negative. The reconstruction is Hermitian. The Hermitian spectral theorem therefore supplies a negative real eigenvalue and a nonzero eigenvector. The result concerns arbitrary complex amplitudes, including zero coordinates; it imposes no restriction on either Schmidt basis.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.U`
- Truth anchor: `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.claim`
- Truth anchor: `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.localConjugation`
- Truth anchor: `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.measured`
- Truth anchor: `D5/S3/Quantum/Tomography/KanachovaLiuTuPureStateDetection.result`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](../Entanglement/AbsolutePPT/Bipartite.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound](../Entanglement/AbsoluteSeparability/SymmetricAbsolutePPTPureBound.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
