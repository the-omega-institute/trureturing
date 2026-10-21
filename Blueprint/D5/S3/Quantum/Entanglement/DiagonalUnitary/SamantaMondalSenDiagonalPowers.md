# Conjugation symmetry of diagonal-unitary powers

## Abstract

Diagonal phase gates have equal multipartite entangling and disentangling powers.

Amplitudes are functions from Fin N → Fin 2 to ℂ. The source maxima are represented by suprema over normalized-state subtypes. The overlap is dotProduct (star φ) ψ, with star acting coordinatewise. A bipartition has two nonempty parts. This includes formal N = 0 and N = 1 cases; the multipartite interpretation concerns N ≥ 2.

**Definition 1.1 (Fully separable pure states).**

$$\forall (N: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), ((\operatorname{IsFullySeparable}\left(\psi\right)) \Leftrightarrow ((\sum_{x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))} (\operatorname{Complex}.\operatorname{normSq}\left(\psi\left(x\right)\right)) = 1) \land (\exists (p: (\operatorname{Fin}\left(N\right) \to (\operatorname{Fin}\left(2\right) \to \mathbb{C}))), (\forall (x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))), (\psi\left(x\right) = \prod_{i: \operatorname{Fin}\left(N\right)} (p\left(i, x\left(i\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.IsFullySeparable` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 2, Eq. (1): “E_N(U) = max_{|ψ⟩_FS^N ∈ S_N} G(U|ψ⟩_FS^N)”, where |ψ⟩_FS^N = ⊗_{i=1}^{N} |ψ_i⟩ is fully separable and S_N is the set of fully separable states. The amplitudes factor as a product of local amplitudes p i (x i), and the sum of squared moduli is one.

**Definition 1.2 (Pure states separable across a bipartition).**

$$\forall (N: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), ((\operatorname{IsBiseparable}\left(\psi\right)) \Leftrightarrow ((\sum_{x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))} (\operatorname{Complex}.\operatorname{normSq}\left(\psi\left(x\right)\right)) = 1) \land (\exists (A: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right)), ((\operatorname{Finset}.\operatorname{Nonempty}\left(A\right)) \land ((\operatorname{Finset}.\operatorname{Nonempty}\left(A^{c}\right)) \land (\exists (a: ((\{i: \operatorname{Fin}\left(N\right) // i \in A\} \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), (\exists (b: ((\{i: \operatorname{Fin}\left(N\right) // i \in A^{c}\} \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), (\forall (x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))), (\psi\left(x\right) = a\left(((i: \{i: \operatorname{Fin}\left(N\right) // i \in A\}) \mapsto x\left(\operatorname{val}\left(i\right)\right))\right) \cdot b\left(((i: \{i: \operatorname{Fin}\left(N\right) // i \in A^{c}\}) \mapsto x\left(\operatorname{val}\left(i\right)\right))\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.IsBiseparable` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 6, Appendix A.1: “generalized geometric measure (GGM) which is defined as G(|ψ⟩) = 1 − max_{|ϕ⟩∈S_nG} |⟨ϕ|ψ⟩|², where S_nG denotes the set of all non-genuinely multipartite entangled states.” For pure states, this is factorization across some A and its complement with both parts nonempty. The functions a and b take the restricted computational-basis labels; val denotes subtype inclusion.

**Definition 1.3 (Generalized geometric measure).**

$$\forall (N: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), (\operatorname{G}\left(\psi\right) = 1 - \operatorname{iSup}\left(((\phi: \{v: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}) // \operatorname{IsBiseparable}\left(v\right)\}) \mapsto \operatorname{Complex}.\operatorname{normSq}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(\operatorname{val}\left(\phi\right)\right), \psi\right)\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.G` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 6, Appendix A.1: “generalized geometric measure (GGM) which is defined as G(|ψ⟩) = 1 − max_{|ϕ⟩∈S_nG} |⟨ϕ|ψ⟩|², where S_nG denotes the set of all non-genuinely multipartite entangled states.” Here iSup is the real supremum over the displayed subtype and Complex.normSq is the squared complex modulus.

**Definition 1.4 (Multipartite entangling power).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{E}\left(U\right) = \operatorname{iSup}\left(((\psi: \{v: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C}) // \operatorname{IsFullySeparable}\left(v\right)\}) \mapsto \operatorname{G}\left(\operatorname{Matrix}.\operatorname{mulVec}\left(U, \operatorname{val}\left(\psi\right)\right)\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.E` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 2, Eq. (1): “E_N(U) = max_{|ψ⟩_FS^N ∈ S_N} G(U|ψ⟩_FS^N)”. The input family consists of normalized fully separable amplitudes. Matrix.mulVec is the matrix action, and iSup represents the maximum as a supremum.

**Definition 1.5 (Multipartite disentangling power).**

$$\forall (N: \mathbb{N}), (\forall (U: \operatorname{Matrix}\left((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)), \mathbb{C}\right)), (\operatorname{D}\left(U\right) = \operatorname{E}\left(\operatorname{Matrix}.\operatorname{conjTranspose}\left(U\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.D` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 2, Eq. (2): “D_N(U) ≡ E_N(U†) = max_{|ψ⟩_FS^N ∈ S_N} G(U†|ψ⟩_FS^N)”. The adjoint is Matrix.conjTranspose.

**Definition 1.6 (The Appendix B.3 expectation).**

$$(claim) \Leftrightarrow (\forall (N: \mathbb{N}), (\forall (\theta: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{R})), (\operatorname{E}\left(\operatorname{Matrix}.\operatorname{diagonal}\left(((x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))) \mapsto \operatorname{Complex}.\operatorname{exp}\left((\theta\left(x\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right))\right)\right) = \operatorname{D}\left(\operatorname{Matrix}.\operatorname{diagonal}\left(((x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))) \mapsto \operatorname{Complex}.\operatorname{exp}\left((\theta\left(x\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right))\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.claim` (`✓ std3`).

*Citation.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Page 8, Appendix B.3: “It also indicates that such an equivalence may hold for arbitrary diagonal unitary operators acted on arbitrary number of qubits.” The variable N is the number of qubits; θ assigns a real phase to every computational-basis label. The diagonal entries are Complex.exp (θ x * Complex.I).

**Theorem 1.7 (Equality for every diagonal phase gate).**

$$\forall (N: \mathbb{N}), (\forall (\theta: ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{R})), (\operatorname{E}\left(\operatorname{Matrix}.\operatorname{diagonal}\left(((x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))) \mapsto \operatorname{Complex}.\operatorname{exp}\left((\theta\left(x\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right))\right)\right) = \operatorname{D}\left(\operatorname{Matrix}.\operatorname{diagonal}\left(((x: (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))) \mapsto \operatorname{Complex}.\operatorname{exp}\left((\theta\left(x\right): \mathbb{C}) \cdot \operatorname{Complex}.\operatorname{I}\right))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* M. Samanta; S. Mondal; A. Sen (De) (2025). *Disparity between multipartite entangling and disentangling powers of unitaries: Even vs Odd*. DOI: [10.48550/arXiv.2505.18539](https://doi.org/10.48550/arXiv.2505.18539). URL: <https://arxiv.org/abs/2505.18539v1>.

*Commentary.*

Coordinatewise conjugation preserves normalization and both product factorizations. It conjugates the overlap, preserving its squared modulus, and therefore preserves G. For diagonal U it satisfies U.conjTranspose.mulVec (star ψ) = star (U.mulVec ψ). Conjugation bijects the fully separable inputs, so the two families of values have the same supremum. No hypothesis about attainment or local phases is required.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.D`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.E`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.G`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.IsBiseparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.IsFullySeparable`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/DiagonalUnitary/SamantaMondalSenDiagonalPowers.result`
