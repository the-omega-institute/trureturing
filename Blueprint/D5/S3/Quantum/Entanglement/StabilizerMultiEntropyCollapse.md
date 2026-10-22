# The ternary replica collapse for four-party stabilizer states

## Abstract

For a normalized pure qubit stabilizer state, ternary replica contractions are positive real numbers. Their four-party genuine multi-entropy is determined by the tripartite information.

Akella and Gadde, Rényi multi-entropy of graph states and the n → 1 limit, arXiv:2610.27080v1 (19 October 2026), Section II Eqs. (7)–(9) and Appendix A, give an odd-replica rank formula that also implies this n=3 four-party relation. For the three nonzero F₄ labels, diagonal rescaling makes the rank depend only on their equality partition. The entropy normalization here retains n^{−(q−2)}, which their Eq. (2) explicitly omits. The partition counts then give the coefficient 1/9. This is a structural formal proof and reusable library growth for an existing conclusion, with no new unique-solve or global-priority claim. The resolution slug below preserves the existing project resolution; the open counting question in arXiv:2607.06050v2 Section 6 is a source-text statement, not a current no-other-proof certificate.

**Definition 1.1 (Shifting a replica coordinate).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), \forall (c : \operatorname{Fin}\left(q\right)), \forall (r : (\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right))), \operatorname{shift}\left(n, q, c, r\right) = (i : \operatorname{Fin}\left((q - 1)\right)) \mapsto \operatorname{ite}\left((i : \mathbb{N}) = (c : \mathbb{N}), \operatorname{r}\left(i\right) + 1, \operatorname{r}\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.shift` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Replica labels are functions Fin(q − 1) → ℤ/nℤ. The shift adds one at the coordinate whose natural index equals the colour c. Colour q − 1 has no such coordinate and acts as the identity. Natural differences such as q − 1 and q − 2 in these formulas use truncated subtraction.

**Definition 1.2 (Contracting the replicas).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{Z}\left(n, q, col, \psi\right) = \sum_{(x : ((\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right)) \to (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right))))} \prod_{(r : (\operatorname{Fin}\left((q - 1)\right) \to \operatorname{ZMod}\left(n\right)))} \operatorname{star}\left(\psi(\operatorname{x}\left(r\right))\right) \cdot \psi(((u : \operatorname{Fin}\left(N\right)) \mapsto \operatorname{x}\left(\operatorname{shift}\left(n, q, \operatorname{col}\left(u\right), r\right), u\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

A configuration x assigns a binary N-qubit string to each replica label r. The conjugated amplitude is evaluated at x(r); the other amplitude takes qubit u from the replica shifted by its colour col(u). Summing the product gives the computational-basis contraction of Appendix A.

**Definition 1.3 (The normalized multi-entropy).**

$$\forall (n : \mathbb{N}), \forall (q : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{S}\left(n, q, col, \psi\right) = \frac{1}{(1 - (n : \mathbb{R}))} \cdot \frac{1}{(n : \mathbb{R})^{(q - 2)}} \cdot \operatorname{log}\left(\operatorname{Re}\left(\frac{\operatorname{Z}\left(n, q, col, \psi\right)}{\operatorname{Z}\left(1, q, col, \psi\right)^{n^{(q - 1)}}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.S` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The normalization divides Z(n,q,col,ψ) by the indicated power of Z(1,q,col,ψ). The logarithm is applied to the real part of the quotient, with the prefactors specified in Appendix A. The casts of n to ℝ appear explicitly.

**Definition 1.4 (Four cuts minus three cuts).**

$$\forall (n : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{I3}\left(n, party, \psi\right) = \operatorname{S}\left(n, 2, (([0, 0, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 0, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([1, 0, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) - (\operatorname{S}\left(n, 2, (([0, 0, 1, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.I3` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

Label A, B, C, D by 0, 1, 2, 3. Each displayed tuple is a function from Fin 4 to the stated colour set, composed with party. In order, the four positive terms are ABC:D, ABD:C, ACD:B and BCD:A; the three subtracted terms are AB:CD, AC:BD and AD:BC. This is the Rényi tripartite information I₍₃,n₎ in Eq. (1) of the paper.

**Definition 1.5 (The genuine four-party combination).**

$$\forall (n : \mathbb{N}), [\operatorname{NeZero}\left(n\right)], \forall (a : \mathbb{R}), \forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{GM4}\left(n, a, party, \psi\right) = \operatorname{S}\left(n, 4, party, \psi\right) - \frac{1}{3} \cdot (\operatorname{S}\left(n, 3, (([0, 0, 1, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([0, 1, 0, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([0, 1, 2, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 0, 0, 2] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 0, 2, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 3, (([1, 2, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))) \circ party), \psi\right)) + \frac{1}{3} \cdot (\operatorname{S}\left(n, 2, (([0, 0, 0, 1] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 0, 1, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([0, 1, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right) + \operatorname{S}\left(n, 2, (([1, 0, 0, 0] : (\operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(2\right))) \circ party), \psi\right)) - a \cdot \operatorname{I3}\left(n, party, \psi\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.GM4` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The six three-colour tuples merge AB, AC, AD, BC, BD and CD, respectively. Their entropies have coefficient −1/3, while the four singleton cuts have coefficient 1/3. The remaining term is −a times the tripartite information, for an arbitrary real parameter a, as in §2 of the paper.

**Definition 1.6 (Positivity and the n = 3 collapse).**

$$claim \Leftrightarrow (\forall (N : \mathbb{N}), \forall (party : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(4\right))), \forall (\psi : ((\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)) \to \mathbb{C})), \operatorname{StabilizedBy}\left(pauliSet, \psi\right) \Rightarrow (\sum_{(x : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(2\right)))} \left\lVert \psi(x) \right\rVert^{2} = 1 \Rightarrow ((\forall (q : \mathbb{N}), \forall (col : (\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(q\right))), 0 < \operatorname{Re}\left(\operatorname{Z}\left(3, q, col, \psi\right)\right) \land (\operatorname{Im}\left(\operatorname{Z}\left(3, q, col, \psi\right)\right) = 0)) \land (\forall (a : \mathbb{R}), \operatorname{GM4}\left(3, a, party, \psi\right) = -(a - \frac{1}{9}) \cdot \operatorname{I3}\left(3, party, \psi\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.claim` (`✓ std3`).

*Citation.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

The proposition quantifies over every qubit count, every assignment to four labelled parties and every amplitude. Its two assumptions are Pauli stabilization and unit squared norm. The first conclusion includes every colour count and colouring and asserts both strict positivity of the real part and a zero imaginary part. The second conclusion is Eq. (3) for every real a, with I₃ interpreted as I₍₃,₃₎. Empty parties are allowed.

**Theorem 1.7 (The stabilizer collapse).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result` (`✓ std3`). ∎

*Resolves.* `Problems/akella-2026-stabilizer-multi-entropy-n3-collapse` (proved) by `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akella-2026-stabilizer-multi-entropy-n3-collapse","declaration_gid":"D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Akella, N. Iizuka, A. Miyata (2026). *Genuine Multi-Entropy in the Toric Code*. DOI: [10.48550/arXiv.2607.06050](https://doi.org/10.48550/arXiv.2607.06050). URL: <https://arxiv.org/abs/2607.06050v2>.

*Commentary.*

A stabilizer state is a scalar multiple of a local-unitary image of the unnormalized graphAmp Γ, which has 2^N entries of modulus one, hence squared Hilbert norm 2^N (graph_norm). For arbitrary N including 0, odd n ≥ 3, q ≥ 2, colouring col : Fin N → Fin q, binary matrix Γ and local unitaries U, if ψ = c • (tensorOp U *ᵥ graphAmp Γ) has unit squared Hilbert norm, tensor unitarity preserves Hilbert norm, so normalization fixes the squared modulus star c * c = ((2 : ℂ)^N)⁻¹ (graph_scalar_norm). Under these hypotheses, local-unitary invariance (Z_local_scalar) and homogeneity (Z_smul) give Z(n,q,col,ψ) = (((2 : ℂ)^N)⁻¹)^(n^(q − 1)) · Z(n,q,col,graphAmp Γ). Each of the n^(q − 1) replicas contributes star c * c, giving total degree 2 · n^(q − 1) in the amplitude and its conjugate; under the same hypotheses the prefactor is the reciprocal of 2^(N · n^(q − 1)), hence 1 for N = 0, with empty parties allowed. Here c is arbitrary before normalization; a scalar multiplying a norm-one graph state is a phase of modulus one when the resulting state is also normalized. At n = 3, the graph replica translation form decomposes into bilinear blocks indexed by opposite nonzero Fourier modes. A block contributes the inverse power of two determined by its rank, giving positive real contractions. Each rank depends only on the equality partition of the party colours. TernaryPartitionOrbit identifies nonzero anchored modes with the same partition exactly up to sign, so choosing one mode from each opposite pair chooses each induced partition once. For an arbitrary surjective merger of labels, a colouring with a partition containing the merger kernel factors through the quotient; subtracting the quotient colouring's value at its chosen target anchor restores the zero colour without changing its partition. This gives a bijection between the lower-dimensional mode partitions and the compatible four-party partitions, and transports sums of arbitrary weights along that bijection. With four labels, a nonzero mode whose fourth label is anchored at zero induces neither the discrete four-block partition nor the indiscrete one-block partition. The finite partition coefficients 1, −1, 2 and 1 for the full term, six pair mergers, four singleton cuts and three balanced cuts cancel at every induced partition. Thus the weighted identity holds for any choice of opposite-mode representatives and any function of the separation matrix; the concrete 13, 4 and 1 representatives merely instantiate it. Applying that identity to the block ranks and the entropy normalizations gives the coefficient 1/9 in the displayed collapse. The partition coefficients are checked over the fifteen four-label partitions; this is not a claim of a general coefficient formula for arbitrary party counts. These positivity and entropy conclusions remain restricted to n = 3, and the four-party collapse does not settle the paper's conjecture at other replica or party counts.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.GM4`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.I3`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.S`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.Z`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropyCollapse.shift`
- Dependency: [D5/S3/Combinatorics/Partitions/TernaryPartitionOrbit](../../Combinatorics/Partitions/TernaryPartitionOrbit.md)
- Dependency: [D5/S3/QuadraticForms/TernaryTranslationQuadraticNormalForm](../../QuadraticForms/TernaryTranslationQuadraticNormalForm.md)
- Dependency: [D5/S3/Quantum/Information/BinaryStabilizerGraphNormalForm](../Information/BinaryStabilizerGraphNormalForm.md)
