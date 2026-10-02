# The separable numerical range of one two-qubit observable

## Abstract

For a single two-qubit observable A, the length of the separable numerical range is at least half the length of the numerical range, and the projector onto (|00> + |11>)/sqrt(2) attains one half. This proves Conjecture 8 of T. Simnacher, J. Czartowski, K. Szymański and K. Życzkowski (arXiv:2107.04365): the minimal volume ratio mu_{2,1} equals 1/2.

**Definition 1.1 (Two-qubit states).**

$$\forall \rho : \mathbb{C}^{4\times4}, \rho \in \operatorname{states} \Leftrightarrow (\rho \ge 0 \land \operatorname{Tr}\left(\rho\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.states` (`✓ std3`).

*Citation.* Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski (2021). *Confident entanglement detection via the separable numerical range*. DOI: [10.1103/PhysRevA.104.042420](https://doi.org/10.1103/PhysRevA.104.042420). URL: <https://arxiv.org/abs/2107.04365v1>.

*Commentary.*

A two-qubit state is a complex matrix indexed by pairs of bits that is positive semidefinite and has trace 1.

**Definition 1.2 (Separable states).**

$$\forall \rho : \mathbb{C}^{4\times4}, \rho \in \operatorname{separableStates} \Leftrightarrow (\operatorname{separableCone}\left(\rho\right) \land \operatorname{Tr}\left(\rho\right) = 1)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.separableStates` (`✓ std3`).

*Citation.* Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski (2021). *Confident entanglement detection via the separable numerical range*. DOI: [10.1103/PhysRevA.104.042420](https://doi.org/10.1103/PhysRevA.104.042420). URL: <https://arxiv.org/abs/2107.04365v1>.

*Commentary.*

A separable two-qubit state is a state that is a finite sum of Kronecker products of positive semidefinite 2 x 2 matrices; equivalently, a convex combination of product states.

**Definition 1.3 (Restricted numerical ranges).**

$$\forall X \subseteq \mathbb{C}^{4\times4}, \forall A : \mathbb{C}^{4\times4}, \operatorname{numericalRange}\left(X, A\right) = \ \{\operatorname{Re}\left(\operatorname{Tr}\left(\rho A\right)\right) \mid \rho \in X\ \}$$

*Formalization.* `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.numericalRange` (`✓ std3`).

*Citation.* Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski (2021). *Confident entanglement detection via the separable numerical range*. DOI: [10.1103/PhysRevA.104.042420](https://doi.org/10.1103/PhysRevA.104.042420). URL: <https://arxiv.org/abs/2107.04365v1>.

*Commentary.*

For a set X of states and a matrix A, the restricted numerical range L_X(A) is the set of real parts of Tr(rho A) over rho in X. For Hermitian A and a state rho the trace is real.

**Definition 1.4 (The conjecture).**

$$claim \Leftrightarrow (\operatorname{IsLeast}\left(\ \{\frac{\operatorname{vol}\left(\operatorname{numericalRange}\left(\operatorname{separableStates}, A\right)\right)}{\operatorname{vol}\left(\operatorname{numericalRange}\left(\operatorname{states}, A\right)\right)} \mid A \in \mathbb{C}^{4\times4}, A^{*} = A \land \operatorname{vol}\left(\operatorname{numericalRange}\left(\operatorname{states}, A\right)\right) \ne 0\ \}, \frac{1}{2}\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.claim` (`✓ std3`).

*Citation.* Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski (2021). *Confident entanglement detection via the separable numerical range*. DOI: [10.1103/PhysRevA.104.042420](https://doi.org/10.1103/PhysRevA.104.042420). URL: <https://arxiv.org/abs/2107.04365v1>.

*Commentary.*

One half is the least value of vol L_Sep(A) / vol L(A) over Hermitian two-qubit matrices A with vol L(A) not zero, where vol is Lebesgue measure on the real line. For scalar A both ranges are points, so the ratio is defined exactly when A is not scalar. The least value is attained, so it is the minimum of the paper's Definition 2 for n = 2, d = 2 and k = 1.

**Theorem 1.5 (The minimal ratio is one half).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result` (`✓ std3`). ∎

*Resolves.* `Problems/simnacher-2021-two-qubit-separable-numerical-range-ratio` (proved) by `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"simnacher-2021-two-qubit-separable-numerical-range-ratio","declaration_gid":"D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Timo Simnacher; Jakub Czartowski; Konrad Szymański; Karol Życzkowski (2021). *Confident entanglement detection via the separable numerical range*. DOI: [10.1103/PhysRevA.104.042420](https://doi.org/10.1103/PhysRevA.104.042420). URL: <https://arxiv.org/abs/2107.04365v1>.

*Commentary.*

In the magic basis a two-qubit vector u is a product vector exactly when the sum of the squares of its four coordinates vanishes. After a phase, a unit vector z has z^T z = C with 0 <= C <= 1. For a real unit vector r orthogonal to the real part of z, the vectors z + i t r with t = -eta +- sqrt(eta^2 + C), eta = (Im z) . r, are product vectors, and a convex combination of their projectors equals zz^* + C rr^T; so zz^* + C rr^T is separable. For two unit vectors u and v, two orthonormal real vectors r and s orthogonal to the real parts of both give one separable noise N = (rr^T + ss^T)/2 with trace 1, and with c = max(C_u, C_v) the matrices (P_u + cN)/(1 + c) and (P_v + cN)/(1 + c) are separable states whose difference is (P_u - P_v)/(1 + c). Hence the expectation values of A at two pure states differ by at most 2 times the length of L_Sep(A); by the spectral decomposition of states the same holds for any two states, so vol L(A) <= 2 vol L_Sep(A), using that L_Sep(A) is an interval. For the Bell projector, L(A) contains [0, 1] and every product state has expectation (1/2) times the sum over a, b of sigma_ab tau_ab, which lies in [0, 1/2]; so the ratio is at most 1/2, and therefore equal to 1/2.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.numericalRange`
- Truth anchor: `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.separableStates`
- Truth anchor: `D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.states`
