# The sharp A|BC constant of the GHZ measure

## Abstract

The GHZ measure has sharp bound one half on arbitrary A|BC product density states.

Fin k denotes the k computational labels, indexed from zero. QubitMatrix is Matrix (Fin 2) (Fin 2) Complex and TwoQubitMatrix is Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) Complex. The three-qubit matrix index is Fin 2 × (Fin 2 × Fin 2). Real triples use the Euclidean dotProduct(a,b) = sum over i : Fin 3 of a(i)b(i), not the supremum norm of functions. toLp(2,a) puts the coordinates a into EuclideanSpace Real (Fin 3); vecCons(a,vecCons(b,vecEmpty)) is the two-vector family indexed by Fin 2. Orthonormal Real requires both squared Euclidean lengths to be one and their dot product to vanish. blochMatrix is D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix; at trace parameter zero and coordinates toLp(2, fun i => 2*n(i)), it has entries n(2), n(0) - I*n(1), n(0) + I*n(1), -n(2), read by rows, the Pauli spin expression in equation (1). The symbols a1,a2,b1,b2,c1,c2 represent Lean's subscripted direction names. ofReal explicitly embeds a real scalar into Complex, smul is scalar multiplication, kronecker is Matrix.kroneckerMap with scalar multiplication, trace is the complex matrix trace, re is the real part and sSup is the real supremum. Anonymous square brackets display Lean typeclass assumptions. All formulas bind every parameter; fixed imported operators are named constants.

**Definition 1.1 (Arbitrary density matrices).**

$$\forall n \in \mathit{Type},\; [\mathrm{Fintype}\left(n\right)] \forall rho \in \mathrm{Matrix}\left(n, n, \mathit{Complex}\right),\; \mathrm{IsDensity}\left(\mathit{rho}\right) \Leftrightarrow ((\mathrm{PosSemidef}\left(\mathit{rho}\right)) \land (\mathrm{trace}\left(\mathit{rho}\right) = 1))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

A density matrix is positive semidefinite with complex trace one. The finite index type n is arbitrary, so both single-qubit and two-qubit mixed states are included.

**Definition 1.2 (Real trace expectation).**

$$\forall n \in \mathit{Type},\; [\mathrm{Fintype}\left(n\right)] [\mathrm{DecidableEq}\left(n\right)] \forall rho \in \mathrm{Matrix}\left(n, n, \mathit{Complex}\right),\; \forall A \in \mathrm{Matrix}\left(n, n, \mathit{Complex}\right),\; \mathrm{expect}\left(\mathit{rho}, A\right) = \mathrm{re}\left(\mathrm{trace}\left(A \cdot \mathit{rho}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.expect` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

Section I, printed page 2: “For a unit vector n⃗ ∈ R³, the spin observable on a single qubit is σ_n⃗ = n⃗ · σ = n_x σ_x + n_y σ_y + n_z σ_z, with σ_x, σ_y, σ_z the standard Pauli matrices. For three direction labels n⃗_a, n⃗_b, n⃗_c we denote the tripartite local observable σ(n⃗_a, n⃗_b, n⃗_c) = σ_n⃗_a ⊗ σ_n⃗_b ⊗ σ_n⃗_c, (1) and its expectation ⟨σ(n⃗_a, n⃗_b, n⃗_c)⟩ = Tr[σ(n⃗_a, n⃗_b, n⃗_c)ρ_ABC].” The real part is explicit in Lean; for the Hermitian observables and density matrices in the bound, the imaginary part is zero.

**Definition 1.3 (The three-qubit tensor observable).**

$$\forall a \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall b \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall c \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \mathrm{observable}\left(a, b, c\right) = \mathrm{kronecker}\left(\mathrm{blochMatrix}\left(0, \mathrm{toLp}\left(2, \lambda i:\mathrm{Fin}\left(3\right),2 \cdot a\left(i\right)\right)\right), \mathrm{kronecker}\left(\mathrm{blochMatrix}\left(0, \mathrm{toLp}\left(2, \lambda i:\mathrm{Fin}\left(3\right),2 \cdot b\left(i\right)\right)\right), \mathrm{blochMatrix}\left(0, \mathrm{toLp}\left(2, \lambda i:\mathrm{Fin}\left(3\right),2 \cdot c\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.observable` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

Section I, printed page 2, equation (1): “For a unit vector n⃗ ∈ R³, the spin observable on a single qubit is σ_n⃗ = n⃗ · σ = n_x σ_x + n_y σ_y + n_z σ_z, with σ_x, σ_y, σ_z the standard Pauli matrices. For three direction labels n⃗_a, n⃗_b, n⃗_c we denote the tripartite local observable σ(n⃗_a, n⃗_b, n⃗_c) = σ_n⃗_a ⊗ σ_n⃗_b ⊗ σ_n⃗_c, (1) and its expectation ⟨σ(n⃗_a, n⃗_b, n⃗_c)⟩ = Tr[σ(n⃗_a, n⃗_b, n⃗_c)ρ_ABC].” The tensor is associated as A tensor (B tensor C), retaining all three independent directions.

**Definition 1.4 (Three-body correlation).**

$$\forall rho \in \mathrm{Matrix}\left((\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), (\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), \mathit{Complex}\right),\; \forall a \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall b \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall c \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \mathrm{E}\left(\mathit{rho}, a, b, c\right) = \mathrm{expect}\left(\mathit{rho}, \mathrm{observable}\left(a, b, c\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.E` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

The expectation of the observable in equation (1), with the real part written explicitly.

**Definition 1.5 (The independent-frame functional).**

$$\forall rho \in \mathrm{Matrix}\left((\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), (\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), \mathit{Complex}\right),\; \forall a1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall a2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall b1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall b2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall c1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \forall c2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \mathrm{Istar}\left(\mathit{rho}, \mathit{a1}, \mathit{a2}, \mathit{b1}, \mathit{b2}, \mathit{c1}, \mathit{c2}\right) = \mathrm{E}\left(\mathit{rho}, \mathit{a1}, \mathit{b1}, \mathit{c1}\right) - \mathrm{E}\left(\mathit{rho}, \mathit{a1}, \mathit{b2}, \mathit{c2}\right) \cdot \mathrm{E}\left(\mathit{rho}, \mathit{a2}, \mathit{b1}, \mathit{c2}\right) \cdot \mathrm{E}\left(\mathit{rho}, \mathit{a2}, \mathit{b2}, \mathit{c1}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.Istar` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

Section V.B, printed page 6, equation (27): “The fix is to allow each party its own orthonormal frame. Let (â₁, â₂), (b̂₁, b̂₂), (ĉ₁, ĉ₂) be orthonormal pairs on A, B, C, and set I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ) = ⟨σ_â₁ σ_b̂₁ σ_ĉ₁⟩ − ⟨σ_â₁ σ_b̂₂ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₁ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₂ σ_ĉ₁⟩, (27) the natural independent-frame analogue of (2) (here σ_â σ_b̂ σ_ĉ abbreviates σ_â ⊗ σ_b̂ ⊗ σ_ĉ).” Every direction assignment in all four correlators is retained.

**Definition 1.6 (All orthonormal-frame absolute values).**

$$\forall rho \in \mathrm{Matrix}\left((\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), (\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), \mathit{Complex}\right),\; \mathrm{values}\left(\mathit{rho}\right) = \{v:\mathit{Real}\mid\exists a1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \exists a2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \exists b1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \exists b2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \exists c1 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; \exists c2 \in (\mathrm{Fin}\left(3\right)\to\mathit{Real}),\; (\mathrm{Orthonormal}\left(\mathit{Real}, \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{a1}\right), \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{a2}\right), \mathit{vecEmpty}\right)\right)\right)) \land ((\mathrm{Orthonormal}\left(\mathit{Real}, \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{b1}\right), \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{b2}\right), \mathit{vecEmpty}\right)\right)\right)) \land ((\mathrm{Orthonormal}\left(\mathit{Real}, \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{c1}\right), \mathrm{vecCons}\left(\mathrm{toLp}\left(2, \mathit{c2}\right), \mathit{vecEmpty}\right)\right)\right)) \land (v = \mathrm{abs}\left(\mathrm{Istar}\left(\mathit{rho}, \mathit{a1}, \mathit{a2}, \mathit{b1}, \mathit{b2}, \mathit{c1}, \mathit{c2}\right)\right))))\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.values` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

This set contains every absolute value from equation (27) over the three orthonormal pairs in equation (30). The existential direction parameters all have type Fin 3 → Real.

**Definition 1.7 (The GHZ measure).**

$$\forall rho \in \mathrm{Matrix}\left((\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), (\mathrm{Fin}\left(2\right)\times(\mathrm{Fin}\left(2\right)\times\mathrm{Fin}\left(2\right))), \mathit{Complex}\right),\; \mathrm{EGHZ}\left(\mathit{rho}\right) = \frac{1}{2} \cdot \mathrm{sSup}\left(\mathrm{values}\left(\mathit{rho}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.EGHZ` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

Section V.B, printed page 6, equation (30): “Define the local-unitary invariant measure E_GHZ(ρ) = ½ sup_{â₁⊥â₂, b̂₁⊥b̂₂, ĉ₁⊥ĉ₂} |I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ)|. (30)” The definition is one half times the supremum of values(rho). For every product density in the conclusion this set is nonempty and bounded above.

**Definition 1.8 (The exact A|BC constant).**

$$\mathit{claim} \Leftrightarrow ((\forall rhoA \in \mathit{QubitMatrix},\; \forall rhoBC \in \mathit{TwoQubitMatrix},\; (\mathrm{IsDensity}\left(\mathit{rhoA}\right)) \Rightarrow ((\mathrm{IsDensity}\left(\mathit{rhoBC}\right)) \Rightarrow (\mathrm{EGHZ}\left(\mathrm{kronecker}\left(\mathit{rhoA}, \mathit{rhoBC}\right)\right) \le \frac{1}{2}))) \land (\exists rhoA \in \mathit{QubitMatrix},\; \exists rhoBC \in \mathit{TwoQubitMatrix},\; (\mathrm{IsDensity}\left(\mathit{rhoA}\right)) \land ((\mathrm{IsDensity}\left(\mathit{rhoBC}\right)) \land (\mathrm{EGHZ}\left(\mathrm{kronecker}\left(\mathit{rhoA}, \mathit{rhoBC}\right)\right) = \frac{1}{2}))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.claim` (`✓ std3`).

*Citation.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

Section I, printed page 2, equation (1): “For a unit vector n⃗ ∈ R³, the spin observable on a single qubit is σ_n⃗ = n⃗ · σ = n_x σ_x + n_y σ_y + n_z σ_z, with σ_x, σ_y, σ_z the standard Pauli matrices. For three direction labels n⃗_a, n⃗_b, n⃗_c we denote the tripartite local observable σ(n⃗_a, n⃗_b, n⃗_c) = σ_n⃗_a ⊗ σ_n⃗_b ⊗ σ_n⃗_c, (1) and its expectation ⟨σ(n⃗_a, n⃗_b, n⃗_c)⟩ = Tr[σ(n⃗_a, n⃗_b, n⃗_c)ρ_ABC].” Section V.B, printed page 6, equation (27): “The fix is to allow each party its own orthonormal frame. Let (â₁, â₂), (b̂₁, b̂₂), (ĉ₁, ĉ₂) be orthonormal pairs on A, B, C, and set I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ) = ⟨σ_â₁ σ_b̂₁ σ_ĉ₁⟩ − ⟨σ_â₁ σ_b̂₂ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₁ σ_ĉ₂⟩⟨σ_â₂ σ_b̂₂ σ_ĉ₁⟩, (27) the natural independent-frame analogue of (2) (here σ_â σ_b̂ σ_ĉ abbreviates σ_â ⊗ σ_b̂ ⊗ σ_ĉ).” Section V.B, printed page 6, equation (30): “Define the local-unitary invariant measure E_GHZ(ρ) = ½ sup_{â₁⊥â₂, b̂₁⊥b̂₂, ĉ₁⊥ĉ₂} |I⋆(â₁, â₂, b̂₁, b̂₂, ĉ₁, ĉ₂; ρ)|. (30)” Section V.C, printed page 7, equation (37): “Numerically maximising E_GHZ over all biseparable A|BC states we find the sharp value sup_{ρ ∈ A|BC} E_GHZ(ρ) = ½, (37) attained e.g. by |0⟩_A ⊗ |Φ⁺⟩_BC and coinciding with the product-state value (34); the analytic proof of the exact constant 1/2 remains open. The same 1/2 holds for the B|AC and C|AB partitions by symmetry.” The A|BC class is rhoA kronecker rhoBC with arbitrary density factors. The encoding states the universal upper bound and existence of an attaining density product, which together give the displayed supremum. The B|AC and C|AB symmetry statement and convex-mixture conclusions are outside this claim.

**Theorem 1.9 (The exact constant is one half).**

$$(\forall rhoA \in \mathit{QubitMatrix},\; \forall rhoBC \in \mathit{TwoQubitMatrix},\; (\mathrm{IsDensity}\left(\mathit{rhoA}\right)) \Rightarrow ((\mathrm{IsDensity}\left(\mathit{rhoBC}\right)) \Rightarrow (\mathrm{EGHZ}\left(\mathrm{kronecker}\left(\mathit{rhoA}, \mathit{rhoBC}\right)\right) \le \frac{1}{2}))) \land (\exists rhoA \in \mathit{QubitMatrix},\; \exists rhoBC \in \mathit{TwoQubitMatrix},\; (\mathrm{IsDensity}\left(\mathit{rhoA}\right)) \land ((\mathrm{IsDensity}\left(\mathit{rhoBC}\right)) \land (\mathrm{EGHZ}\left(\mathrm{kronecker}\left(\mathit{rhoA}, \mathit{rhoBC}\right)\right) = \frac{1}{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/wu-zhong-wu-2026-ghz-measure-biseparable-half` (proved) by `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wu-zhong-wu-2026-ghz-measure-biseparable-half","declaration_gid":"D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shengjun Wu; Kaichen Zhong; Jeffery Wu (2026). *A measure for genuine tripartite entanglement*. DOI: [10.48550/arXiv.2605.02876](https://doi.org/10.48550/arXiv.2605.02876). URL: <https://arxiv.org/abs/2605.02876v3>.

*Commentary.*

For a product density, the functional factors as u f11 − u uprime² f22 f12 f21. Variance of a real linear combination of anticommuting Hermitian involutions bounds the sum of their squared expectations by one. Applying this to the two overlapping pairs on the same BC state bounds |f12 f21| by 1−|f11|². Consequently the absolute functional is at most q [x+(1−q²)(1−x²)], where q=|u| and x=|f11|. If 1−q² is at most one half, the bracket is at most one. Otherwise q≤3/4 and the bracket≤5/4, giving at most 15/16. The product |0⟩⟨0| tensor |Φ⁺⟩⟨Φ⁺| attains one half using direction pairs (z,x),(x,z),(x,z). No convexity or bound for mixtures across partitions follows from this conclusion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.E`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.EGHZ`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.IsDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.Istar`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.expect`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.observable`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/GHZMeasureBiseparableBound.values`
- Dependency: [D5/S3/Observer/StateNotPath](../../Observer/StateNotPath.md)
- Dependency: [D5/S3/Quantum/Information/ActualPureQubitGeometry](../Information/ActualPureQubitGeometry.md)
- Dependency: [D5/S3/Quantum/Information/CovarianceSumBound](../Information/CovarianceSumBound.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
