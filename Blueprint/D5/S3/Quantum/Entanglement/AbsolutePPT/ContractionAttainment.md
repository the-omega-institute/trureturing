# Dimension-general APPT contraction attainment

## Abstract

A positive contraction decomposition in arbitrary finite local dimensions supplies a literal five-row APPT attainer.

A positive contraction yields an APPT operator in arbitrary finite local dimensions. In five rows, a rank-2n coordinate projection gives a normalized state of purity 5/(24n). This is a lower-bound construction; a maximum-purity upper bound is not asserted.

The existing ContractionBlocks.separableCone_scalar_add_of_opNorm_le_one theorem gives a stronger separable-cone scalar-shift result for Hermitian Euclidean contractions, and QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef turns that separability into partial-transpose positivity. Ahiable--Kothakonda--Winter, The geometry of absolute separability and other convex matrix properties from spectrum, arXiv:2608.03390v2 (https://arxiv.org/abs/2608.03390v2), supplies the published Eq. (31) APPT condition and Corollary 6.4/Eq. (44) lower bounds and attaining constructions. The ordered-pair derivation below gives the five-row application; it asserts no maximum, uniqueness, or novelty.

Bipartite.partialTranspose has entry M((a,d),(c,b)), and Bipartite.APPT quantifies over every global unitary. KickedIsingNegativityRefutation.partialTranspose and QutritPerturbationAttainment.APPT are definitionally equal to these respective operations, with the same local index types and matrix domains.

**Definition 1.1 (Elementary local operator).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (a:A), \forall (b:A), blockUnit\left(a, b\right)=Matrix.kronecker\left(Matrix.single\left(a, b, (1:\mathbb{C})\right), (1:Matrix\left(B, B, \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.blockUnit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is E_ab tensor I_B. Both local index types are arbitrary finite types, including empty types.

**Definition 1.2 (Symmetric local operator).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (a:A), \forall (b:A), symBlock\left(a, b\right)=(blockUnit\left(a, b\right)+blockUnit\left(b, a\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.symBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both orientations are allowed. On the diagonal the operator equals twice E_aa.

**Definition 1.3 (Antisymmetric local operator).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (a:A), \forall (b:A), antiBlock\left(a, b\right)=(blockUnit\left(a, b\right)-blockUnit\left(b, a\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.antiBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the diagonal the operator is zero; reversing a pair changes its sign.

**Definition 1.4 (First-subsystem transpose).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (X:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), firstTranspose\left(X\right)=Matrix.transpose\left(partialTranspose\left(X\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.firstTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The project's partialTranspose transposes the second subsystem. Full transpose converts it to first-subsystem transpose, with entry X((k,j),(i,l)).

**Definition 1.5 (Positive ordered-pair sum).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (X:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), krausSum\left(X\right)=SMul.smul\left(\frac{1}{2}, \sum_{a:A} \sum_{b:A} (((symBlock\left(a, b\right)\cdot X)\cdot Matrix.conjTranspose\left(symBlock\left(a, b\right)\right))+((antiBlock\left(a, b\right)\cdot (1-X))\cdot Matrix.conjTranspose\left(antiBlock\left(a, b\right)\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.krausSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each ordered pair has weight one half. Combining the two orientations gives one unordered off-diagonal pair. The diagonal contributes 2 E_aa X E_aa, as in the stated ordered-pair sum.

**Theorem 1.6 (Dimension-general Kraus identity).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (X:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), krausSum\left(X\right)=(SMul.smul\left(((Fintype.card\left(A\right):\mathbb{C})-1), 1\right)+SMul.smul\left(2, firstTranspose\left(X\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.kraus_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No Hermitian assumption is used. Expanding a pair leaves the two transpose sandwiches and its constant antisymmetric Gram term. Summing matrix units yields (card A minus one) I plus twice firstTranspose X. All subtractions in the coefficient are complex subtraction, not truncated natural subtraction.

**Theorem 1.7 (PSD contraction consequence).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (X:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), ((Matrix.PosSemidef\left(X\right))\land (Matrix.PosSemidef\left((1-X)\right)))\Rightarrow Matrix.PosSemidef\left((SMul.smul\left(((Fintype.card\left(A\right):\mathbb{C})-1), 1\right)+SMul.smul\left(2, partialTranspose\left(X\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.partial_transpose_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For X PSD and I minus X PSD, every summand is a nonnegative congruence. Taking the full transpose of the Kraus identity gives the project's second-subsystem convention. Zeros, ties and singular contractions are retained. The existing QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef implication is stronger when separability is already available; this declaration supplies the direct PSD-contraction route.

**Theorem 1.8 (All-global-unitary APPT).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (X:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), ((Matrix.PosSemidef\left(X\right))\land (Matrix.PosSemidef\left((1-X)\right)))\Rightarrow APPT\left((SMul.smul\left(((Fintype.card\left(A\right):\mathbb{C})-1), 1\right)+SMul.smul\left(2, X\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.contraction_appt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

APPT is the existing literal predicate over every unitary on A times B. For an arbitrary global U, both UXU* and I minus UXU* are PSD by congruence. Apply the preceding theorem to this conjugated contraction. No supplied unitary family replaces the quantifier. For the five-row reflection, the stronger ContractionBlocks separability theorem together with QuadbitMaximumPurity.separableCone_partialTranspose_posSemidef and the existing Ahiable--Kothakonda--Winter Eq. (31) result supplies a prior separability route; this generic APPT consequence is not presented as unique.

**Definition 1.9 (Two-row coordinate projection).**

$$\forall (n:\mathbb{N}), fiveRowProjector\left(n\right)=Matrix.diagonal\left((fun (p:(Fin\left(5\right)\times Fin\left(n\right))) \mapsto ite\left(Fin.val\left(Prod.fst\left(p\right)\right)<2, 1, 0\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.fiveRowProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly the first two of the five rows are selected, for every coordinate of Fin n. The proof establishes idempotence, positivity of both complementary projections, trace 2n and rank 2n.

**Definition 1.10 (Normalized five-row state).**

$$\forall (n:\mathbb{N}), fiveRowDensity\left(n\right)=SMul.smul\left(Complex.ofReal\left(\frac{1}{(24\cdot (n:\mathbb{R}))}\right), (SMul.smul\left(4, 1\right)+SMul.smul\left(2, fiveRowProjector\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.fiveRowDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n positive the denominator 24n is the numerator's trace: 4 times 5n plus 2 times 2n.

**Theorem 1.11 (Literal five-row attaining family).**

$$\forall (n:\mathbb{N}), (0<n)\Rightarrow (Matrix.rank\left(fiveRowProjector\left(n\right)\right)=(2\cdot n))\land (Matrix.PosSemidef\left(fiveRowDensity\left(n\right)\right))\land (Matrix.trace\left(fiveRowDensity\left(n\right)\right)=1)\land (APPT\left(fiveRowDensity\left(n\right)\right))\land (Complex.re\left(Matrix.trace\left((fiveRowDensity\left(n\right)\cdot fiveRowDensity\left(n\right))\right)\right)=\frac{5}{(24\cdot (n:\mathbb{R}))})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.five_row_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The numerator square is 16 I plus 20 P and has trace 120n. Normalization gives purity 5/(24n). The theorem applies to every positive n, hence to the original n at least five and to its n at least nineteen branch. It proves attainment only. The generic normalized_ray and normalized_basis_diagonal results already cover the other rank-one family and are reused, not duplicated. The published Ahiable--Kothakonda--Winter Corollary 6.4/Eq. (44) already supplies the corresponding lower bound and attainers, so this family is not a new maximum or unique construction. Upper bounds, the physical five-row necessity bridge and classification are not conclusions of this attaining construction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.antiBlock`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.blockUnit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.contraction_appt`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.firstTranspose`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.fiveRowDensity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.fiveRowProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.five_row_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.krausSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.kraus_identity`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.partial_transpose_posSemidef`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment.symBlock`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite](Bipartite.md)
