# A strong-subadditivity counterexample for subentropy

## Abstract

A Bell pair and an independent maximally mixed qubit violate strong subadditivity of subentropy by exactly one twelfth.

Zhang, Singh and Pati ask the following question at arXiv:1510.08859v2, §7.1.

A similarly question can be asked for the strong subadditivity of subentropy: Q(ρ ABC) + Q(ρ B) ⩽ Q(ρ AB) + Q(ρ BC).

The formal conjecture quantifies over all three finite subsystem types and every positive trace-one joint density. Its AB marginal traces out C; its B marginal then traces out A. Its BC marginal uses only the associativity bijection of product labels before tracing out A.

**Definition 1.1 (Reassociating subsystem labels).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.reassocState`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.reassocState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical product associativity equivalence sends ((a,b),c) to (a,(b,c)). The existing InputInformationBalance.relabel applied to the inverse equivalence changes only these labels, allowing the existing bipartite partial trace to produce the BC marginal.

**Definition 1.2 (The maximally mixed qubit).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.uniformTwo`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.uniformTwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix is diagonal on Fin 2 with both diagonal entries equal to one half. It is packaged directly in the canonical density-state carrier.

**Definition 1.3 (The canonical Bell density as a density state).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.bellState`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.bellState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The state wraps the existing CHSHWitness.bellDensity, the outer product of its normalized Bell vector with its conjugate. Positivity and trace one are reused from bell_density_is_state; the existing Bell pure-state theorem supplies normalization and the maximally mixed marginal.

**Definition 1.4 (The three-qubit witness).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.witness`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The joint state is productState bellState uniformTwo. Thus A and B form a Bell pair, while C is an independent maximally mixed qubit. The construction uses the existing Kronecker-product density-state operation.

**Definition 1.5 (The paper's spectral functional family).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.SubentropyLike`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.SubentropyLike` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A family assigns a real value to each finite density state. It is continuous on density states, invariant under unitary conjugation, and agrees with the negative spectral residue sum on diagonal states with positive pairwise distinct entries. All coordinate types lie in Type, and all hypotheses retain their full finite-dimensional quantifiers.

The consumed private identification theorem diagonalizes each density matrix and perturbs its ordered eigenvalues p by (1−ε)p+εq. The vector q has strictly positive decreasing entries proportional to N−i in the eigenvalue ordering; hence each positive perturbation has distinct positive entries and sum one. Taking ε=1/(k+1) gives convergence in the fixed eigenbasis. The spectral-formula theorem identifies both functionals on every approximant, and continuity of both, including continuousOn_matrixSubentropy, identifies their limits. Thus every such family equals subentropy, also at repeated or zero eigenvalues.

canonicalSubentropy constructs an inhabitant from the determinant integral: its continuity uses DensityKernel, its unitary invariance uses isometric embedding, and its diagonal values use SpectralFormula. The result consumes this inhabitant and the identification theorem, so the quantified hypothesis set is nonempty.

**Definition 1.6 (The strong-subadditivity question).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture`

*Formalization.* `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture` (`✓ std3`).

*Citation.* Lin Zhang, Uttam Singh, Arun Kumar Pati (2017). *Average subentropy, coherence and entanglement of random mixed quantum states*. DOI: [10.1016/j.aop.2016.12.024](https://doi.org/10.1016/j.aop.2016.12.024). URL: <https://arxiv.org/abs/1510.08859>.

*Commentary.*

For every SubentropyLike family Q and every finite tripartite density rho, assert Q(rho)+Q(rho_B)≤Q(rho_AB)+Q(rho_BC). Every marginal is constructed from that same joint density with the repository's partial-trace API. The BC reassociation is a pure relabelling, with no replacement state or additional assumption.

**Theorem 1.7 (Strong subadditivity fails with gap one twelfth).**

Lean statement: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-singh-pati-2017-subentropy-strong-subadditivity` (refuted) by `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-singh-pati-2017-subentropy-strong-subadditivity","declaration_gid":"D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lin Zhang, Uttam Singh, Arun Kumar Pati (2017). *Average subentropy, coherence and entanglement of random mixed quantum states*. DOI: [10.1016/j.aop.2016.12.024](https://doi.org/10.1016/j.aop.2016.12.024). URL: <https://arxiv.org/abs/1510.08859>.

*Commentary.*

For the witness, rho_AB is the pure Bell state, rho_B is I₂/2, and rho_BC is I₄/4. The joint state is an isometric embedding of I₂/2. Its embedding matrix has entries J((a,b),c;d)=bellVector(a,b) when c=d and zero otherwise; Bell-vector normalization gives J-adjoint J=I₂.

The determinant identity for rectangular Gram matrices preserves the defining subentropy integral under this embedding. Hence Q(rho)=Q(rho_B)=log 2−1/2, while Q(rho_AB)=0 and Q(rho_BC)=log 4−13/12.

Using log 4=2 log 2 gives Q(rho)+Q(rho_B)−Q(rho_AB)−Q(rho_BC)=1/12. This positive gap contradicts the conjectured inequality. The proof uses one joint positive trace-one density and its actual marginals throughout.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.SubentropyLike`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.bellState`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.reassocState`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.uniformTwo`
- Truth anchor: `D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.witness`
- Dependency: [D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal](../Entanglement/BellPureStateMixedMarginal.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/InputInformationBalance](../Information/InputInformationBalance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Subentropy/DensityKernel](DensityKernel.md)
- Dependency: [D5/S3/Quantum/Subentropy/SpectralFormula](SpectralFormula.md)
- Dependency: [D5/S3/Quantum/Subentropy/UniformValues](UniformValues.md)
