# Whole-cone pair positivity and the common orientation

## Abstract

Positive readbacks of two overlapping pairs force a common transpose orientation on one actual full Hermitian triple.

**Definition 1.1 (The normalized tensor form supplied to Lean).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.TensorNormalForm`

*Formalization.* `D5/S3/Quantum/Foundation/TripleMatrixOrientation.TensorNormalForm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Each actual preparation is supplied with one fixed output unitary and two fixed input transpose bits, with the identity valid on all Hermitian inputs. The external proof input is Jinli Xu, Baodong Zheng and Ajda Fošner, Linear maps preserving tensor products of rank-one Hermitian matrices, J. Aust. Math. Soc. 98 (2015), 407–428, Main Theorem p. 409, (1.1)–(1.2), with Proposition 2.1 pp. 410–411 for a single active factor. Equal dimensions remove zero padding, positivity fixes the sign, and trace normalization on spanning pure products makes the congruence unitary. Lean takes the resulting normalized identities for M and L as explicit hypotheses. https://doi.org/10.1017/S1446788714000603

**Theorem 1.2 (Compose the two actual preparation forms).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.triple_normal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixOrientation.triple_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The inner bits are ε and δ and the outer bits are α and β. The transpose on the whole pair flips the first two local bits together, so the three bits in (32) are α xor ε, α xor δ and β.

**Theorem 1.3 (Identify each retained map on the entire triple).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.retained_pair_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixOrientation.retained_pair_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The all-vector readback and real spanning of both preparations identify the actual linear pair map with the partial trace in permuted coordinates, the induced two-factor transpose mask, and conjugation back to the actual pair. This is the one-sector formula in (33).

**Theorem 1.4 (The partial trace reaches the entire retained PSD cone).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.traceLast_psd_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixOrientation.traceLast_psd_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

Tensor an arbitrary retained PSD matrix with a positive trace-one spectator. The retained input can be entangled.

**Theorem 1.5 (Whole-cone positivity rules out a mixed transpose).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.pairMaskH_bits`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixOrientation.pairMaskH_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

For n at least two, the repository Bell compression supplies a PSD witness whose one-sided partial transpose fails positivity. Full transposition relates the two mixed masks.

**Theorem 1.6 (The three pair parities force the same triple bit).**

Lean statement: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.align_bits`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/TripleMatrixOrientation.align_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and J. Hilgert (2019). *Strongly symmetric spectral convex bodies are Jordan algebra state spaces*. DOI: [10.48550/arXiv.1904.03753](https://doi.org/10.48550/arXiv.1904.03753). URL: <https://arxiv.org/abs/1904.03753v1>.

*Commentary.*

The fixed carriers are H(n), H(n times n) and H((n times n) times n), with the same actual M in both overlapping pair readbacks. The given p13 and p23 must take every PSD matrix on the actual triple to a PSD matrix on the actual pair. With the two normalized forms and both spans, their readbacks give the first two edges of (34). The preparation gives the inner edge. Since the three edges share ε xor δ, this bit is zero and the three triple bits coincide for n at least two.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.TensorNormalForm`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.align_bits`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.pairMaskH_bits`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.retained_pair_formula`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.traceLast_psd_surjective`
- Truth anchor: `D5/S3/Quantum/Foundation/TripleMatrixOrientation.triple_normal`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtBell](../Entanglement/AbsolutePPT/UniformSchmidtBell.md)
- Dependency: [D5/S3/Quantum/Foundation/PositiveMarginalMatrixComposition](PositiveMarginalMatrixComposition.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
