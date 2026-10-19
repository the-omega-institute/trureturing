# The most classical orthonormal basis of spin 3/2

## Abstract

Every orthonormal basis of spin 3/2 has mean one-qubit anticoherence at least 1/9, attained by an explicit classical basis.

**Definition 1.1 (The normalized three-qubit Dicke embedding).**

$$\forall \psi : \operatorname{Fin}\left(4\right) \to \mathbb{C}, \forall a : \operatorname{Fin}\left(2\right), \forall b : \operatorname{Fin}\left(2\right), \forall c : \operatorname{Fin}\left(2\right), \operatorname{dicke}\left(\psi, (a,b,c)\right) = \frac{\psi_{\operatorname{val}\left(a\right) + \operatorname{val}\left(b\right) + \operatorname{val}\left(c\right)}}{\sqrt{\operatorname{binom}\left(3, \operatorname{val}\left(a\right) + \operatorname{val}\left(b\right) + \operatorname{val}\left(c\right)\right)}}$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.dicke` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

Index the angular-momentum basis by k = 0,1,2,3, with magnetic quantum number 3/2 - k. The map dicke sends its kth vector to the normalized uniform superposition of three-qubit bit strings with k ones. Thus a bit string with k ones has amplitude psi_k/sqrt(binom(3,k)). The binomial coefficient counts distinct bit strings, and val denotes the natural value of a bit index. This is the normalized Dicke identification of Eqs. (6)-(8).

**Definition 1.2 (The one-qubit reduced state).**

$$\forall \psi : \operatorname{Fin}\left(4\right) \to \mathbb{C}, \forall c : \operatorname{Fin}\left(2\right), \forall d : \operatorname{Fin}\left(2\right), \left(\rho_{1}\right)\left(\psi\right)_{cd} = \sum_{a \in \operatorname{Fin}\left(2\right)} (\sum_{b \in \operatorname{Fin}\left(2\right)} (\operatorname{dicke}\left(\psi, (a,b,c)\right) \cdot \overline{\operatorname{dicke}\left(\psi, (a,b,d)\right)}))$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.reducedState` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

Write rho_1(psi) for reducedState(psi). The indices a and b are the first two qubits; c and d index the remaining qubit. The sum traces out the first two qubits from the outer product of dicke(psi) with its adjoint, as in Eq. (12). The definition applies to every vector psi; for a unit vector it is a density matrix.

**Definition 1.3 (One-qubit anticoherence).**

$$\forall \psi : \operatorname{Fin}\left(4\right) \to \mathbb{C}, \left(\mathcal{A}_{1}\right)\left(\psi\right) = 2 \cdot (1 - \operatorname{Re}\left(\operatorname{tr}\left((\left(\rho_{1}\right)\left(\psi\right))^{2}\right)\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.anticoherence` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

Denote anticoherence(psi) by A_1(psi). It is twice one minus the purity of rho_1(psi), the t = 1 case of Eqs. (13)-(14). The real part is explicit in the definition; rho_1(psi) is Hermitian, so the trace of its square is real. No normalization hypothesis is imposed on the definition.

**Definition 1.4 (Mean anticoherence of the columns).**

$$\forall U : \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right), \left(\mathcal{B}_{1}\right)\left(U\right) = \frac{1}{4} \cdot \sum_{i \in \operatorname{Fin}\left(4\right)} (\left(\mathcal{A}_{1}\right)\left(U \cdot e_{i}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.basisAnticoherence` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

Denote basisAnticoherence(U) by B_1(U). The vector U e_i is the ith column, where e_i is the standard coordinate vector. The definition takes the arithmetic mean of the four column anticoherences, as in Eq. (15). It is defined for every complex four-by-four matrix; when U is unitary, its columns form an orthonormal basis.

**Definition 1.5 (The attaining matrix of Eq. (21)).**

$$\operatorname{let} \nu : \mathbb{C} := \sqrt{3} \cdot (2 - \sqrt{2}) \operatorname{in} \operatorname{let} \tau : \mathbb{C} := 3 - 2 \cdot \sqrt{2} \operatorname{in} \operatorname{let} \omega : \mathbb{C} := \frac{-1 + i \cdot \sqrt{3}}{2} \operatorname{in} \operatorname{classicalBasis} = \frac{1}{\sqrt{18 \cdot (3 - 2 \cdot \sqrt{2})}} \cdot \begin{pmatrix}1&1&1&\tau \cdot \sqrt{3}\\\nu&\nu \cdot \omega&\nu \cdot \omega^{2}&0\\\nu&\nu \cdot \omega^{2}&\nu \cdot \omega&0\\\tau&\tau&\tau&-\sqrt{3}\end{pmatrix}$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.classicalBasis` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

The matrix classicalBasis is the matrix U_4^c of Eq. (21). The displayed local constants are complex numbers, with positive real square roots embedded in the complex field and i the imaginary unit. The algebraic value of omega is exp(2 pi i/3). Columns are ordered in the angular-momentum coordinates used by the Dicke embedding.

**Definition 1.6 (The minimum and its attainment).**

$$\operatorname{claim} \Leftrightarrow ((\forall U : \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right), (U \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(4\right), \mathbb{C}\right)) \Rightarrow (\frac{1}{9} \le \left(\mathcal{B}_{1}\right)\left(U\right))) \land ((\operatorname{classicalBasis} \in \operatorname{unitaryGroup}\left(\operatorname{Fin}\left(4\right), \mathbb{C}\right)) \land (\left(\mathcal{B}_{1}\right)\left(\operatorname{classicalBasis}\right) = \frac{1}{9})))$$

*Formalization.* `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.claim` (`✓ std3`).

*Citation.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

Every orthonormal basis of the spin-3/2 space has mean one-qubit anticoherence at least 1/9. The matrix of Eq. (21) is unitary and attains 1/9. These are the three parts of claim, expressing Conjecture 1 with the columns of a unitary matrix as the basis vectors.

**Theorem 1.7 (The sharp lower bound and the classical basis).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.result` (`✓ std3`). ∎

*Resolves.* `Problems/rudzinski-burchardt-zyczkowski-2024-spin-three-halves-classical-basis` (proved) by `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rudzinski-burchardt-zyczkowski-2024-spin-three-halves-classical-basis","declaration_gid":"D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marcin Rudziński; Adam Burchardt; Karol Życzkowski (2024). *Orthonormal bases of extreme quantumness*. DOI: [10.22331/q-2024-01-25-1234](https://doi.org/10.22331/q-2024-01-25-1234). URL: <https://arxiv.org/abs/2306.00532v3>.

*Commentary.*

For a unit vector psi, let p(psi) be its spin expectation vector, with components the real expectations of the spin-3/2 operators J_x, J_y and J_z. The Dicke reduction gives A_1(psi) = 1 - 4|p(psi)|^2/9. Consequently, for a unitary U, B_1(U) = 1 - S(U)/9, where S(U) is the sum of the squared lengths of the four column polarizations. Multiplying the first column by the inverse determinant changes neither its reduced state nor its spin expectations, and reduces the bound to matrices of determinant one.

The six-by-six matrix of two-by-two minors acts on the second exterior power of C^4. Its unitarity and its preservation of the signed form coupling complementary two-element subsets make it real orthogonal in a fixed exterior basis. Its columns therefore give a real orthonormal six-frame, grouped into three pairs x_k,y_k. An isometry identifies this real space with R plus the traceless real symmetric three-by-three matrices; write x_k = (s_k,X_k) and y_k = (t_k,Y_k) in these coordinates. The spin action becomes a commutator action, and the zero sum of the column polarizations yields S(U) = 2 sum_{k=1}^3 ||[X_k,Y_k]||_F^2, where [X,Y] = XY - YX and the norm is Frobenius.

Subtracting the component of Y along X in the Böttcher-Wenzel inequality gives the refinement ||[X,Y]||_F^2 <= 2(||X||_F^2 ||Y||_F^2 - <X,Y>_F^2). The frame identities are ||X_k||_F^2 = 1 - s_k^2, ||Y_k||_F^2 = 1 - t_k^2, <X_k,Y_k>_F = -s_k t_k, and sum_{k=1}^3(s_k^2 + t_k^2) = 1. They give S(U) <= 4 sum_{k=1}^3(1 - s_k^2 - t_k^2) = 8, hence B_1(U) >= 1/9.

For the matrix of Eq. (21), exact evaluation proves unitarity and gives the four spin polarizations (4/3,0,sqrt(2)/3), (-2/3,2sqrt(3)/3,sqrt(2)/3), (-2/3,-2sqrt(3)/3,sqrt(2)/3), and (0,0,-sqrt(2)). Their squared lengths are 2 and their pairwise inner products are -2/3, so they are the vertices of a regular tetrahedron. Thus S = 8 and B_1 = 1/9. This proves the minimum asserted in Conjecture 1.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.anticoherence`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.basisAnticoherence`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.classicalBasis`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.dicke`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.reducedState`
- Truth anchor: `D5/S3/Quantum/Measurement/SpinThreeHalvesClassicalBasis.result`
- Dependency: [D5/S3/Quantum/Entanglement/PrecessionSpinOneSeparableBound](../Entanglement/PrecessionSpinOneSeparableBound.md)
- Dependency: [D5/S3/Quantum/Matrix/WeightedBotcherWenzel](../Matrix/WeightedBotcherWenzel.md)
- Dependency: [D5/S3/Quantum/Schatten/CompoundMatrices](../Schatten/CompoundMatrices.md)
