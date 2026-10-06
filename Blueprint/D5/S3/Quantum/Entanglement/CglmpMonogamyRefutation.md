# Two reduced states of one three-qutrit state both violate the CGLMP inequality

## Abstract

Kumari, Ghose and Mann (arXiv:1704.06516, Phys. Rev. A 96, 012128) conjecture, from numerical studies, that the CGLMP inequality is monogamous for qutrits: for every three-qutrit state at most one of the reduced states rho_AB, rho_BC, rho_AC has B_CGLMP > 2, where B_CGLMP maximizes the CGLMP expression I_3 over their Fourier-phase family of measurements. It fails: for v = |002> + |011> + 2|020> + |100> + 2|112> - |121> + 2|210> + 2|222> and rho = v v^dagger / 20, both rho_AB and rho_AC reach I_3 = 1/2 + 14 sqrt 3 / 15 > 2.

**Definition 1.1 (The Fourier transform).**

$$\forall j : \operatorname{Fin}\left(3\right), \forall k : \operatorname{Fin}\left(3\right), dft\left(j, k\right) = \frac{omega^{\operatorname{val}\left(j\right) \cdot \operatorname{val}\left(k\right)}}{\sqrt{3}}$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.dft` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

U_FT is the three-dimensional discrete Fourier transform, with entries omega^{jk}/sqrt 3 where omega = exp(2 pi i/3) is the existing omega; its inverse U_FT^* is the conjugate transpose.

**Definition 1.2 (The phase matrices).**

$$\forall \varphi : \operatorname{Fin}\left(3\right) \to \mathbb{R}, \operatorname{phase}\left(\varphi\right) = \operatorname{diagonal}\left((j \mapsto \exp(-(i \cdot \varphi\left(j\right))))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.phase` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

U(phi) is the diagonal unitary with entries exp(-i phi(j)) for an angle vector phi : Fin 3 -> R.

**Definition 1.3 (Joint outcome probabilities).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall A : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall B : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall j : \operatorname{Fin}\left(3\right), \forall k : \operatorname{Fin}\left(3\right), \operatorname{jointProb}\left(\rho, A, B, j, k\right) = \operatorname{re}\left(\operatorname{tr}\left(\operatorname{kronecker}\left(\operatorname{single}\left(j, j, 1\right), \operatorname{single}\left(k, k, 1\right)\right) \cdot \operatorname{kronecker}\left(A, B\right) \cdot \rho \cdot \operatorname{kronecker}\left(A^{H}, B^{H}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.jointProb` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Eq. (Probabilities): applying A to the first qutrit and B to the second and measuring in the computational basis, outcome (j, k) has probability tr(Pi_j (x) Pi_k (A (x) B) rho (A^dagger (x) B^dagger)), with Pi_j = single(j, j, 1) the projector onto |j>, kronecker the Kronecker product and H the conjugate transpose.

**Definition 1.4 (Event probabilities).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall A : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall B : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall E : \operatorname{Fin}\left(3\right) \to \operatorname{Fin}\left(3\right) \to Prop, \operatorname{eventProb}\left(\rho, A, B, E\right) = \sum_{a, b : E\left(a, b\right)} \operatorname{jointProb}\left(\rho, A, B, a, b\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.eventProb` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

The probability of an event E on the outcome pair is the sum of the joint probabilities of the outcome pairs (a, b) in E.

**Definition 1.5 (The CGLMP expression).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall A_{1}, A_{2}, B_{1}, B_{2} : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{cglmpI3}\left(\rho, A_{1}, A_{2}, B_{1}, B_{2}\right) = \operatorname{eventProb}\left(\rho, A_{1}, B_{1}, ((a, b) \mapsto a = b)\right) + \operatorname{eventProb}\left(\rho, A_{2}, B_{1}, ((a, b) \mapsto b = a + 1)\right) + \operatorname{eventProb}\left(\rho, A_{2}, B_{2}, ((a, b) \mapsto a = b)\right) + \operatorname{eventProb}\left(\rho, A_{1}, B_{2}, ((a, b) \mapsto b = a)\right) - \operatorname{eventProb}\left(\rho, A_{1}, B_{1}, ((a, b) \mapsto a = b - 1)\right) - \operatorname{eventProb}\left(\rho, A_{2}, B_{1}, ((a, b) \mapsto b = a)\right) - \operatorname{eventProb}\left(\rho, A_{2}, B_{2}, ((a, b) \mapsto a = b - 1)\right) - \operatorname{eventProb}\left(\rho, A_{1}, B_{2}, ((a, b) \mapsto b = a - 1)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.cglmpI3` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Eq. (CGLMP1): I_3 = P(A_1 = B_1) + P(B_1 = A_2 + 1) + P(A_2 = B_2) + P(B_2 = A_1) - P(A_1 = B_1 - 1) - P(B_1 = A_2) - P(A_2 = B_2 - 1) - P(B_2 = A_1 - 1), with outcomes added modulo 3 in Fin 3.

**Definition 1.6 (The CGLMP expression at given angles).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall (\theta_{1}, \theta_{2}) : (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}), \operatorname{cglmpAt}\left(\rho, (\theta_{1}, \theta_{2})\right) = \operatorname{cglmpI3}\left(\rho, dft \cdot \operatorname{phase}\left(\left(\theta_{1}\right)\left(0\right)\right), dft \cdot \operatorname{phase}\left(\left(\theta_{1}\right)\left(1\right)\right), dft^{H} \cdot \operatorname{phase}\left(\left(\theta_{2}\right)\left(0\right)\right), dft^{H} \cdot \operatorname{phase}\left(\left(\theta_{2}\right)\left(1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.cglmpAt` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

cglmpAt(rho, theta) is I_3 of rho at the twelve angles theta = (theta_1, theta_2), with A_k = U_FT U(phi_k) for phi_k = theta_1(k) and B_l = U_FT^* U(phi'_l) for phi'_l = theta_2(l). Eq. (CGLMP2) takes B_CGLMP(rho) to be its maximum over theta.

**Definition 1.7 (The CGLMP value of a state).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \forall b : \mathbb{R}, (\operatorname{IsCglmpValue}\left(\rho, b\right)) \Leftrightarrow ((\exists \theta : (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}), \operatorname{cglmpAt}\left(\rho, \theta\right) = b) \land (\forall \theta : (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(3\right) \to \mathbb{R}), \operatorname{cglmpAt}\left(\rho, \theta\right) \le b))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.IsCglmpValue` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Eq. (CGLMP2): b is B_CGLMP(rho) when b is the greatest value of cglmpAt(rho, theta) over all angles theta, that is, the maximum of I_3 over the twelve angles.

**Definition 1.8 (The reduced state on AB).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{rhoAB}\left(\rho\right) = \operatorname{partialTraceRight}\left(\operatorname{submatrix}\left(\rho, (((a, b), c) \mapsto (a, b, c)), (((a, b), c) \mapsto (a, b, c))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoAB` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

For a three-qutrit matrix indexed by (a, b, c), rho_AB traces out C: the existing partialTraceRight applied to rho re-indexed by ((a, b), c) -> (a, b, c).

**Definition 1.9 (The reduced state on BC).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{rhoBC}\left(\rho\right) = \operatorname{partialTraceLeft}\left(\rho\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoBC` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

rho_BC traces out A with the existing partialTraceLeft.

**Definition 1.10 (The reduced state on AC).**

$$\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), \operatorname{rhoAC}\left(\rho\right) = \operatorname{partialTraceRight}\left(\operatorname{submatrix}\left(\rho, (((a, c), b) \mapsto (a, b, c)), (((a, c), b) \mapsto (a, b, c))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoAC` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

rho_AC traces out B: the existing partialTraceRight applied to rho re-indexed by ((a, c), b) -> (a, b, c), so that A is measured with A_k and C with B_l.

**Definition 1.11 (The conjectured monogamy).**

$$(claim) \Leftrightarrow (\forall \rho : \operatorname{Matrix}\left(\operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right) \times \operatorname{Fin}\left(3\right), \mathbb{C}\right), ((\operatorname{PosSemidef}\left(\rho\right)) \land (\operatorname{tr}\left(\rho\right) = 1)) \Rightarrow (\forall b_{AB}, b_{BC}, b_{AC} : \mathbb{R}, (((\operatorname{IsCglmpValue}\left(\operatorname{rhoAB}\left(\rho\right), b_{AB}\right)) \land (\operatorname{IsCglmpValue}\left(\operatorname{rhoBC}\left(\rho\right), b_{BC}\right))) \land (\operatorname{IsCglmpValue}\left(\operatorname{rhoAC}\left(\rho\right), b_{AC}\right))) \Rightarrow ((2 < b_{AB}) \Rightarrow ((b_{BC} \le 2) \land (b_{AC} \le 2)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.claim` (`✓ std3`).

*Citation.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Eq. (35): for every three-qutrit state rho_ABC, that is every positive semidefinite 27 x 27 matrix of trace one, and for the maxima b_AB, b_BC, b_AC of I_3 on rho_AB, rho_BC, rho_AC, b_AB > 2 implies b_BC <= 2 and b_AC <= 2.

**Definition 1.12 (The counterexample vector).**

$$stateVec = |002\rangle + |011\rangle + 2 \cdot |020\rangle + |100\rangle + 2 \cdot |112\rangle + -|121\rangle + 2 \cdot |210\rangle + 2 \cdot |222\rangle$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.stateVec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

The unnormalized vector has squared norm 1 + 1 + 4 + 1 + 4 + 1 + 4 + 4 = 20; every basis state |abc> in its support has a - b - c = 1 modulo 3.

**Definition 1.13 (The counterexample state).**

$$rho = \frac{1}{20} \cdot \operatorname{vecMulVec}\left(stateVec, \operatorname{star}\left(stateVec\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

The state is the rank-one density matrix v v^dagger / 20.

**Definition 1.14 (The angle unit).**

$$\forall n : \mathbb{N}, \operatorname{ang}\left(n\right) = \frac{n \cdot \pi}{6}$$

*Formalization.* `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.ang` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Angles are integer multiples of pi/6, so every phase is a twelfth root of unity.

**Theorem 1.15 (Both reduced states violate the inequality).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kumari-2017-cglmp-monogamy` (refuted) by `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kumari-2017-cglmp-monogamy","declaration_gid":"D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Meenu Kumari, Shohini Ghose, Robert B. Mann (2017). *Sufficient condition for nonexistence of symmetric extension of qudits using Bell inequalities*. DOI: [10.1103/PhysRevA.96.012128](https://doi.org/10.1103/PhysRevA.96.012128). URL: <https://arxiv.org/abs/1704.06516v2>.

*Commentary.*

Each joint probability of a reduced state of v v^dagger / 20 is one twentieth of a sum of squared amplitudes, which are sums of twelfth roots of unity divided by 3. With angles in units of pi/6, phi_1 = (0, 2, 7), phi_2 = (0, 2, 1), phi'_1 = (0, 8, 4), phi'_2 = (0, 10, 2) on rho_AB and phi_1 = (0, 6, 9), phi_2 = (0, 6, 3), phi'_1 = (0, 10, 2), phi'_2 = (0, 0, 6) on rho_AC give, in the order of Eq. (CGLMP1), the event probabilities 23/60 + sqrt 3/5, 23/60 + sqrt 3/5, 1/2, 1/2, 23/60 - sqrt 3/5, 23/60 - sqrt 3/5, 1/4 - sqrt 3/15, 1/4 - sqrt 3/15, so I_3 = 1/2 + 14 sqrt 3/15 > 2 for both. For every two-qutrit matrix, I_3 is continuous in the angles and unchanged when an angle moves by 2 pi, so it attains its maximum on the compact box [0, 2 pi]^24; each maximum of rho_AB and rho_AC is therefore at least the stated value. The state is positive semidefinite with trace one.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.IsCglmpValue`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.ang`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.cglmpAt`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.cglmpI3`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.dft`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.eventProb`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.jointProb`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.phase`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rho`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoAB`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoAC`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.rhoBC`
- Truth anchor: `D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.stateVec`
- Dependency: [D5/S3/Quantum/Entanglement/QutritThresholdSharing](QutritThresholdSharing.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Recovery/FiniteLocalLatitudeGeometry](../Recovery/FiniteLocalLatitudeGeometry.md)
