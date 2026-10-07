# Zero-magic-gap three-dimensional subspaces in every power-of-two dimension

## Abstract

For every qudit dimension divisible by four, and so for every power of two at least four, some three-dimensional subspace has zero average stabilizer entropy gap.

**Definition 1.1 (The displacement phase).**

$$\operatorname{tau}\left(d\right) = -\operatorname{exp}\left(\frac{\pi i}{d}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.tau` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

The phase τ = −e^{iπ/d} of the displacement operators, as in §II.A of arXiv:2512.23013v1.

**Definition 1.2 (The displacement operators).**

$$\forall a: \mathbb{Z}/d\mathbb{Z} \times \mathbb{Z}/d\mathbb{Z}, \operatorname{paperDisplacement}\left(d, a\right) = \operatorname{tau}\left(d\right)^{a_{1} \times a_{2}} \cdot \operatorname{displacement}\left(d, a_{1}, a_{2}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.paperDisplacement` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

D_a = τ^{a₁a₂} X^{a₁} Z^{a₂} for a = (a₁, a₂) in (ℤ/dℤ)². The word X^{a₁} Z^{a₂} is the frozen Weyl displacement of D5/S3/Quantum/Algebra/WeylDisplacement, built from the shift X|k⟩ = |k + 1⟩ and the clock Z|k⟩ = ω^k|k⟩, ω = e^{2πi/d}, of D5/S3/Observer/WindowRegister; the phase does not affect any quantity below because each operator occurs together with its adjoint.

**Definition 1.3 (The fourth tensor power).**

$$\operatorname{power4}\left(V\right) = \operatorname{productMap}\left(i \mapsto V\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.power4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V^{⊗4} for a rectangular matrix V, written with the frozen fourfold product productMap of D5/S3/Quantum/Recovery/PurifiedLocalPath, whose entry at (x, y) is the product over the four factors of the entries at (x_i, y_i).

**Definition 1.4 (The alternating fourfold product).**

$$\operatorname{alt}\left(A\right) = \operatorname{productMap}\left(A, (A)^{*}, A, (A)^{*}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.alt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ⊗ A† ⊗ A ⊗ A†, the summand of Q.

**Definition 1.5 (The permutation operators).**

$$\operatorname{T}\left(H, \sigma\right)(x, y) = \operatorname{ite}\left(x = y \circ \sigma^{-1}, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.T` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

T_σ permutes the four tensor factors of a fourfold tensor power over a finite index type H (it is the permutation matrix of the induced permutation of index tuples); the paper writes T_σ = Σ |σ(i,j,k,l)⟩⟨ijkl|.

**Definition 1.6 (The stabilizer entropy operator).**

$$\operatorname{Q}\left(d\right) = d^{-2} \cdot \sum_{a} \operatorname{alt}\left(\operatorname{paperDisplacement}\left(d, a\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.Q` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

Q = d^{-2} Σ_a (D_a ⊗ D_a†)^{⊗2}, so that the linear stabilizer entropy of a pure state is M(ψ) = 1 − d tr(Q ψ^{⊗4}).

**Definition 1.7 (The Haar fourth moment in closed form).**

$$\operatorname{A4}\left(H\right) = \operatorname{binom}\left(\Vert H \Vert + 3, 4\right)^{-1} \cdot \frac{1}{24} \cdot \sum_{\sigma \in S4} \operatorname{T}\left(H, \sigma\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.A4` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

A₄ is the paper's closed form of the Haar average E_U[(UψU†)^{⊗4}], the normalized projector onto the symmetric subspace of four tensor factors. The module takes this closed form as the definition; the Schur–Weyl identity with the Haar integral is quoted from the paper and not formalized.

**Definition 1.8 (The average extrinsic term).**

$$\operatorname{score}\left(V\right) = dB \times \operatorname{tr}\left(\operatorname{Q}\left(dB\right) \operatorname{power4}\left(V\right) \operatorname{A4}\left(\operatorname{Fin}\left(3\right)\right) (\operatorname{power4}\left(V\right))^{*}\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.score` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

For an isometry V from ℂ³ into ℂ^{d_B}, the term d_B tr(Q_B E^{⊗4}(A₄)) of the gap, with E(ρ) = VρV†.

**Definition 1.9 (The average stabilizer entropy gap).**

$$\operatorname{aseGap}\left(V\right) = 3 \times \operatorname{tr}\left(\operatorname{Q}\left(3\right) \operatorname{A4}\left(\mathbb{Z}/3\mathbb{Z}\right)\right) - \operatorname{score}\left(V\right)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.aseGap` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

ΔM(E) = d_S tr(Q_S A₄) − d_B tr(Q_B E^{⊗4}(A₄)) for d_S = 3, as in §III of the paper.

**Definition 1.10 (The power-of-two observation).**

$$claim \Leftrightarrow (\forall m: \mathbb{N}, 2 \leq m \Rightarrow \exists V: \operatorname{Matrix}\left(\mathbb{Z}/2^{m}\mathbb{Z}, \operatorname{Fin}\left(3\right), \mathbb{C}\right), (V)^{*} \times V = 1 \land \operatorname{aseGap}\left(V\right) = 0)$$

*Formalization.* `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.claim` (`✓ std3`).

*Citation.* S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd (2025). *Stabilizer Entropy of Subspaces*. DOI: [10.48550/arXiv.2512.23013](https://doi.org/10.48550/arXiv.2512.23013). URL: <https://arxiv.org/abs/2512.23013v1>.

*Commentary.*

The observation of §V.A of arXiv:2512.23013v1, "when d_B is a power of 2, a zero ASE subspace of dimension three is always achievable": for every m ≥ 2 some isometry from ℂ³ into ℂ^{2^m} has zero gap (ℂ² has no three-dimensional subspace).

**Theorem 1.11 (Every power of two at least four has a zero-gap three-dimensional subspace).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/cepollaro-2025-power-of-two-zero-magic-gap` (proved) by `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cepollaro-2025-power-of-two-zero-magic-gap","declaration_gid":"D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The proof gives more: write d_B = 4r and take the subspace spanned by |r⟩, |3r⟩ and (|0⟩ − |2r⟩)/√2. Its vectors are supported on the subgroup rℤ_{4r}, so X^a Z^b compresses to zero unless r divides a, and for a = ur it compresses to the ququart operator X^u Z^{b mod 4}, each residue of b having r lifts; hence the extrinsic term equals that of the ququart subspace span{|1⟩, |3⟩, (|0⟩ − |2⟩)/√2} for every r. The sixteen compressed 3 × 3 operators have fourth moments 1 (once), 1/5 (three times) and 1/15 (twelve times), computed from the permutation sum over the 24 elements of S₄, so the extrinsic term is (1 + 3/5 + 12/15)/4 = 3/5; the qutrit term is (1 + 8/10)/3 = 3/5. The gap vanishes, and 2^m = 4 · 2^{m−2} for m ≥ 2.

## References

- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.A4`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.Q`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.T`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.alt`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.aseGap`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.claim`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.paperDisplacement`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.power4`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.result`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.score`
- Truth anchor: `D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap.tau`
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementPowers](../Algebra/WeylDisplacementPowers.md)
- Dependency: [D5/S3/Quantum/Algebra/WeylDisplacementTrace](../Algebra/WeylDisplacementTrace.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../Recovery/PurifiedLocalPath.md)
