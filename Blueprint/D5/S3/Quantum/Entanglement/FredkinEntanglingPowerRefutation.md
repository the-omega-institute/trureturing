# The four-qubit Fredkin gate generates more than two ebits across AD:BC

## Abstract

The four-qubit Fredkin gate F_4 generates more than two ebits across the cut AD:BC: one product input with auxiliary systems gives 2.00034... ebits. This refutes the conjecture of X. Qiu, Z. Song and L. Chen (arXiv:2410.15253) that the entanglement generation K_AD:BC(F_4) equals two ebits.

**Definition 1.1 (A party with its auxiliary system).**

$$\operatorname{Party}\left(d\right) = (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(d\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.Party` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

Each of the parties A, B, C and D is a qubit together with a local auxiliary system of dimension d, so its basis labels are pairs (q, r) with q in Fin 2 and r in Fin d.

**Definition 1.2 (The SWAP gate).**

$$swapGate = \operatorname{toMatrix}\left(\operatorname{toPEquiv}\left(\operatorname{prodComm}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.swapGate` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The SWAP gate S_2 on two qubits is the permutation matrix of the map (c, d) -> (d, c): its entry at row (c, d) and column (c', d') is 1 when (c', d') = (d, c) and 0 otherwise.

**Definition 1.3 (The four-qubit Fredkin gate).**

$$fredkin4 = \operatorname{kronecker}\left(\operatorname{single}\left((0, 0), (0, 0), 1\right) + \operatorname{single}\left((0, 1), (0, 1), 1\right) + \operatorname{single}\left((1, 0), (1, 0), 1\right), 1\right) + \operatorname{kronecker}\left(\operatorname{single}\left((1, 1), (1, 1), 1\right), swapGate\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.fredkin4` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The paper's gate F_4 = (|00><00| + |01><01| + |10><10|)_AB tensor I_CD + |11><11|_AB tensor (S_2)_CD on the qubit labels ((a, b), (c, d)). Here single(i, i, 1) is the matrix unit |i><i| and kronecker is the Kronecker product of matrices.

**Definition 1.4 (The output amplitudes).**

$$\operatorname{output}\left(\psi_{A}, \psi_{B}, \psi_{C}, \psi_{D}\right)\left((((a, r_{A}), (d, r_{D})), ((b, r_{B}), (c, r_{C})))\right) = \sum_{((s, t), (u, v))} fredkin4\left(((a, b), (c, d)), ((s, t), (u, v))\right) \cdot \left(\psi_{A}\right)\left(s, r_{A}\right) \cdot \left(\psi_{B}\right)\left(t, r_{B}\right) \cdot \left(\psi_{C}\right)\left(u, r_{C}\right) \cdot \left(\psi_{D}\right)\left(v, r_{D}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.output` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The amplitudes of (F_4 tensor I_R)(psi_A tensor psi_B tensor psi_C tensor psi_D), indexed by the cut A R_A D R_D : B R_B C R_C. The label (((a, r_A), (d, r_D)), ((b, r_B), (c, r_C))) collects the qubits a, b, c, d and the auxiliary labels r_A, r_B, r_C, r_D; F_4 acts on the qubits and the identity acts on the auxiliary systems. The sum runs over all qubit labels ((s, t), (u, v)).

**Definition 1.5 (Entanglement generated from product inputs).**

$$generatedEntanglement = \{E \in \mathbb{R} \mid \exists d_{A}, d_{B}, d_{C}, d_{D} \in \mathbb{N}, \exists \psi_{A} : \operatorname{Party}\left(d_{A}\right) \to \mathbb{C}, \exists \psi_{B} : \operatorname{Party}\left(d_{B}\right) \to \mathbb{C}, \exists \psi_{C} : \operatorname{Party}\left(d_{C}\right) \to \mathbb{C}, \exists \psi_{D} : \operatorname{Party}\left(d_{D}\right) \to \mathbb{C}, \exists \rho : \operatorname{DensityState}\left(((\operatorname{Party}\left(d_{A}\right) \times \operatorname{Party}\left(d_{D}\right)) \times (\operatorname{Party}\left(d_{B}\right) \times \operatorname{Party}\left(d_{C}\right)))\right), (\operatorname{dotProduct}\left(\operatorname{star}\left(\psi_{A}\right), \psi_{A}\right) = 1) \land \left((\operatorname{dotProduct}\left(\operatorname{star}\left(\psi_{B}\right), \psi_{B}\right) = 1) \land \left((\operatorname{dotProduct}\left(\operatorname{star}\left(\psi_{C}\right), \psi_{C}\right) = 1) \land \left((\operatorname{dotProduct}\left(\operatorname{star}\left(\psi_{D}\right), \psi_{D}\right) = 1) \land \left((\forall i j, \rho\left(i, j\right) = \operatorname{output}\left(\psi_{A}, \psi_{B}, \psi_{C}, \psi_{D}\right)\left(i\right) \cdot \operatorname{star}\left(\operatorname{output}\left(\psi_{A}, \psi_{B}, \psi_{C}, \psi_{D}\right)\left(j\right)\right)) \land (E = \frac{\operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\rho\right)\right)}{\log 2})\right)\right)\right)\right)\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.generatedEntanglement` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The values, in ebits, of the entanglement across A R_A D R_D : B R_B C R_C of an output of F_4: for auxiliary dimensions d_A, d_B, d_C, d_D, unit inputs psi_A, psi_B, psi_C, psi_D (the sum of the conjugate of psi_i times psi_i is 1), and the pure output state rho with entries output(i) times the conjugate of output(j), the von Neumann entropy -Tr(sigma log sigma) of the reduced state sigma = marginalRight(rho) on A R_A D R_D, divided by log 2. DensityState, vonNeumannEntropy and marginalRight are the existing definitions of density states (positive semidefinite matrices of trace 1), of the von Neumann entropy and of the partial trace over the right factor.

**Definition 1.6 (The entanglement generation K_AD:BC(F_4)).**

$$entanglementGeneration = \operatorname{sSup}\left(generatedEntanglement\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.entanglementGeneration` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The supremum of the generated entanglement over all auxiliary dimensions and all unit product inputs, as in the paper's definition of the multipartite entangling power for the fixed bipartition AD:BC.

**Definition 1.7 (The conjectured value two ebits).**

$$claim \Leftrightarrow (entanglementGeneration = 2)$$

*Formalization.* `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.claim` (`✓ std3`).

*Citation.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

The conjecture of the paper: the entanglement generation of F_4 across AD:BC is exactly two ebits. The paper proves that it lies between 2 and log_2 5.

**Theorem 1.8 (An input that generates more than two ebits).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/qiu-2025-fredkin-entangling-power` (refuted) by `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"qiu-2025-fredkin-entangling-power","declaration_gid":"D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xinyu Qiu; Zhiwei Song; Lin Chen (2025). *Multipartite entangling power by von Neumann entropy*. DOI: [10.1103/PhysRevA.111.022407](https://doi.org/10.1103/PhysRevA.111.022407). URL: <https://arxiv.org/abs/2410.15253v1>.

*Commentary.*

Take psi_A = (3|0> + 20|1>)/sqrt(409) and psi_B = sqrt(2/75)|0> + sqrt(73/75)|1> with one-dimensional auxiliary systems, and psi_C = psi_D = (|00> + |01> + |10> - |11>)/2 on a qubit and an auxiliary qubit. The output amplitude matrix M across the cut factors as D_A N D_B with D_A, D_B diagonal and N rational, so M M^* has the characteristic polynomial of the rational matrix N (D_B D_B^*) N^T (D_A^* D_A). A kernel-checked computation writes this matrix as P diag(mu) P^(-1) with rational P, so the reduced state has eigenvalues mu = (1752, 1460, 1460, 1460, 3, 0, 0, 0)/6135 and trace 1. The existing spectral lemmas turn the von Neumann entropy into the sum of -mu log mu over these eigenvalues. Writing each term through log(6135/(4k)) and bounding log(6135/5840) and log(6135/7008) by their Taylor polynomials with remainder, and log(6135/12) > 6 by e < 2.7182818286, gives an entropy above 2 log 2, that is 2.00034... > 2 ebits. The generated entanglement then contains a value above 2: if it is bounded above, its supremum exceeds 2; otherwise the supremum is 0. In either case K_AD:BC(F_4) is not 2.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.Party`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.entanglementGeneration`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.fredkin4`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.generatedEntanglement`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.output`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/FredkinEntanglingPowerRefutation.swapGate`
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Information/InputInformationBalance.md)
