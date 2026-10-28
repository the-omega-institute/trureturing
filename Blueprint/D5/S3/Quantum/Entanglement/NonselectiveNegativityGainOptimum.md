# The optimal negativity of a non-selective two-qubit measurement

## Abstract

For every pure two-qubit state, the largest negativity after a non-selective projective measurement is half its initial negativity plus one quarter.

Vectors have complex coordinates indexed by Fin(2) × Fin(2), and operators are complex matrices on this product index. The symbol Uᴴ denotes the conjugate transpose, star denotes coordinatewise complex conjugation, and normSq is the squared complex modulus. The trace norm is the sum of singular values. The negativity is $\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{negativity}\left(\rho\right) = \frac{\left\lVert (\rho)^{\Gamma} \right\rVert_{1} - 1}{2})$. Here Γ is partial transposition on the second factor: the entry with row (i, j) and column (k, l) becomes the original entry with row (i, l) and column (k, j).

The rank-one density ψψ†, also written ψψᴴ, is `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`. Its entries are ψ(i) times the conjugate of ψ(j); for a unit vector it is the pure-state density matrix.

**Definition 1.1 (The non-selective measurement map).**

$$\forall (U: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\forall (\rho: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{measured}\left(U, \rho\right) = \sum_{j: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))} (\operatorname{smul}\left((((U)^{H} \cdot \rho) \cdot U)\left(j, j\right), \operatorname{vecMulVec}\left(((i: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto U\left(i, j\right)), \operatorname{star}\left(((i: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))) \mapsto U\left(i, j\right))\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.measured` (`✓ std3`).

*Citation.* Margherita Zuppardo; Ray Ganardi; Marek Miller; Somshubhro Bandyopadhyay; Tomasz Paterek (2019). *Entanglement gain in measurements with unknown results*. DOI: [10.1103/PhysRevA.99.042319](https://doi.org/10.1103/PhysRevA.99.042319). URL: <https://arxiv.org/abs/1806.05465v1>.

*Commentary.*

Theorem 2 gives the post-measurement state as the sum of the basis projectors weighted by the squared overlaps with the input vector. Here the columns u_j of U give those basis vectors, and the coefficient is (UᴴρU)_jj. For unitary U and ρ = ψψ† this is |⟨u_j, ψ⟩|². The definition itself accepts arbitrary matrices U and ρ; smul denotes scalar multiplication.

**Definition 1.2 (The global two-qubit negativity optimum).**

$$(claim) \Leftrightarrow (\forall (\psi: ((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)) \to \mathbb{C})), ((\sum_{i: (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right))} (\operatorname{normSq}\left(\psi\left(i\right)\right)) = 1) \Rightarrow ((\forall (U: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((U \in \operatorname{unitaryGroup}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) \Rightarrow (\operatorname{negativity}\left(\operatorname{measured}\left(U, \psi \cdot (\psi)^{H}\right)\right) \le \frac{\operatorname{negativity}\left(\psi \cdot (\psi)^{H}\right)}{2} + \frac{1}{4}))) \land (\exists (U: \operatorname{Matrix}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), ((U \in \operatorname{unitaryGroup}\left((\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)), \mathbb{C}\right)) \land (\operatorname{negativity}\left(\operatorname{measured}\left(U, \psi \cdot (\psi)^{H}\right)\right) = \frac{\operatorname{negativity}\left(\psi \cdot (\psi)^{H}\right)}{2} + \frac{1}{4}))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.claim` (`✓ std3`).

*Citation.* Margherita Zuppardo; Ray Ganardi; Marek Miller; Somshubhro Bandyopadhyay; Tomasz Paterek (2019). *Entanglement gain in measurements with unknown results*. DOI: [10.1103/PhysRevA.99.042319](https://doi.org/10.1103/PhysRevA.99.042319). URL: <https://arxiv.org/abs/1806.05465v1>.

*Commentary.*

For every unit two-qubit vector ψ, every unitary U satisfies N(measured(U, ψψ†)) ≤ N(ψψ†)/2 + 1/4, and some unitary U attains equality. Here N denotes the negativity defined above. Section I.E obtains this value within the family of measurement bases in Eq. (28), through Eq. (33), and asks whether it is optimal over all measurement bases. The two clauses state that global bound and its attainment.

**Theorem 1.3 (The sharp bound and an attaining measurement).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/zuppardo-ganardi-miller-bandyopadhyay-paterek-2018-nonselective-negativity-optimum` (proved) by `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zuppardo-ganardi-miller-bandyopadhyay-paterek-2018-nonselective-negativity-optimum","declaration_gid":"D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Margherita Zuppardo; Ray Ganardi; Marek Miller; Somshubhro Bandyopadhyay; Tomasz Paterek (2019). *Entanglement gain in measurements with unknown results*. DOI: [10.1103/PhysRevA.99.042319](https://doi.org/10.1103/PhysRevA.99.042319). URL: <https://arxiv.org/abs/1806.05465v1>.

*Commentary.*

Let ρ = ψψ† for a unit vector and let σ = measured(U, ρ) = Σ_j p_j P_j, where P_j are the orthogonal rank-one column projectors of a unitary U. Orthogonality gives Tr(σ²) = Σ_j p_j² = Tr(σρ). Since ρ² = ρ and Tr(ρ) = 1, it follows that Tr((2σ − ρ)²) = 1. Thus the Hermitian matrix X = 2σ − ρ has Frobenius norm one.

Partial transposition permutes the matrix entries, so it preserves the Frobenius norm. In dimension four the Hilbert–Schmidt Hölder inequality gives ‖Y‖₁ ≤ 2‖Y‖_F, hence ‖X^Γ‖₁ ≤ 2. The triangle inequality applied to 2σ^Γ = ρ^Γ + X^Γ yields 2‖σ^Γ‖₁ ≤ ‖ρ^Γ‖₁ + 2. Substitution into the definition of negativity gives N(σ) ≤ N(ρ)/2 + 1/4.

For attainment, the Schmidt decomposition gives local coordinates ψ₀ = a|00⟩ + b|11⟩ with a, b nonnegative and a² + b² = 1. A real orthogonal measurement basis in the span of |00⟩ and |11⟩, completed by |01⟩ and |10⟩, gives the half-pure, half-Bell state σ₀ = (ψ₀ψ₀† + ΦΦ†)/2, where Φ = (|00⟩ + |11⟩)/√2. Its partially transposed eigenvalues are a²/2 + 1/4, b²/2 + 1/4, ab/2 + 1/4, and −(ab/2 + 1/4). Consequently N(σ₀) = ab/2 + 1/4 = N(ψ₀ψ₀†)/2 + 1/4. Local unitaries transport this measurement back to ψ and preserve negativity. This attaining state is the construction of Theorem 3; together with the bound it establishes the global optimality asked in Section I.E.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.measured`
- Truth anchor: `D5/S3/Quantum/Entanglement/NonselectiveNegativityGainOptimum.result`
- Truth anchor: `D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment](AbsolutePPT/QutritPerturbationAttainment.md)
- Dependency: [D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM](TavakoliMorelliIncompleteEAM.md)
- Dependency: [D5/S3/QuantumBounds/NegativityReductionInclusionRefutation](../../QuantumBounds/NegativityReductionInclusionRefutation.md)
