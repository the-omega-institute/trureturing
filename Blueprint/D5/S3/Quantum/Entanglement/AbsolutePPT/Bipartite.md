# Generic bipartite matrix primitives

## Abstract

Shared product-matrix primitives preserve the existing second-factor transpose and universal APPT meanings.

Second-factor partial transpose acts on matrices indexed by a product of local types. APPT requires positivity after every global unitary conjugation. These definitions enter the dimension-general contraction decomposition and the five-row attaining family.

**Definition 1.1 (Second-factor partial transpose).**

$$\forall (A:Type), \forall (B:Type), \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), \forall (p:(A\times B)), \forall (q:(A\times B)), partialTranspose\left(M, p, q\right)=M\left(Prod.mk\left(Prod.fst\left(p\right), Prod.snd\left(q\right)\right), Prod.mk\left(Prod.fst\left(q\right), Prod.snd\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary local index types A and B, the output entry at ((a,b),(c,d)) is the input entry at ((a,d),(c,b)). No finiteness, decidable equality, equal-cardinality, Hermitian or positivity assumption is imposed. The operation is definitionally equal to KickedIsingNegativityRefutation.partialTranspose over the same Type-star telescope.

**Definition 1.2 (All-unitary partial-transpose positivity).**

$$\forall (A:Type), \forall (B:Type), [Fintype\left(A\right)] [Fintype\left(B\right)] [DecidableEq\left(A\right)] [DecidableEq\left(B\right)] \forall (M:Matrix\left((A\times B), (A\times B), \mathbb{C}\right)), APPT\left(M\right)\iff \forall (U:unitaryGroup\left((A\times B), \mathbb{C}\right)), Matrix.PosSemidef\left(partialTranspose\left(((val\left(U\right)\cdot M)\cdot Matrix.conjTranspose\left(val\left(U\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.APPT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair of finite local types with Fintype and DecidableEq instances, APPT M says that the second-factor partial transpose of U M U-adjoint is positive semidefinite for every global unitary on A times B. Empty and unequal local dimensions remain admitted. The Type-star telescope and full unitary group are exactly those of QutritPerturbationAttainment.APPT, which is definitionally equal to this predicate. ContractionAttainment.contraction_appt and five_row_attainment use this predicate.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.APPT`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/Bipartite.partialTranspose`
