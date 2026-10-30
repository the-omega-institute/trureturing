# Qutrit APPT attaining states

## Abstract

Explicit rank-one and projector perturbations attain the two candidate qutrit APPT purities.

APPT is definitionally equal to Bipartite.APPT over the same finite local types and their Fintype and DecidableEq instances. Both predicates require partial-transpose positivity after every global unitary, including on empty systems.

**Definition 1.1 (Rank-one perturbation).**

$$\forall (n:\mathbb{N}), \forall (v:(Fin\left(3\right)\times Fin\left(n\right))\to \mathbb{C}), rhoPure\left(n, v\right)=SMul.smul\left(Complex.ofReal\left(\frac{1}{3\cdot (n:\mathbb{R})+2}\right), (1+SMul.smul\left(2, Matrix.vecMulVec\left(v, star\left(v\right)\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.rhoPure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar coefficient is Complex.ofReal of a real quotient. The numeral one is the identity Matrix. The vector is indexed by Fin 3 × Fin n and star acts pointwise.

**Definition 1.2 (Projector perturbation).**

$$\forall (n:\mathbb{N}), \forall (P:Matrix\left((Fin\left(3\right)\times Fin\left(n\right)), (Fin\left(3\right)\times Fin\left(n\right)), \mathbb{C}\right)), rhoProjector\left(n, P\right)=SMul.smul\left(Complex.ofReal\left(\frac{1}{4\cdot (n:\mathbb{R})}\right), (1+P)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.rhoProjector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar is Complex.ofReal of the real quotient 1/(4n). This definition does not itself assume that P is an orthogonal projector.

**Theorem 1.3 (Conjugating a rank-one outer product).**

$$\forall (I:Type), [Fintype\left(I\right)] \forall (A:Matrix\left(I, I, \mathbb{C}\right)), \forall (v:I\to \mathbb{C}), A\cdot Matrix.vecMulVec\left(v, star\left(v\right)\right)\cdot Matrix.conjTranspose\left(A\right)=Matrix.vecMulVec\left(Matrix.mulVec\left(A, v\right), star\left(Matrix.mulVec\left(A, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.conjugate_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This dimension-independent identity is extracted from the original attainment proof. It identifies conjugation by an arbitrary square matrix with applying that matrix to the vector. The original qutrit attainment and the quadbit maximum proof reuse this same declaration.

**Theorem 1.4 (A unitary preserves vector normalization).**

$$\forall (I:Type), [Fintype\left(I\right)] [DecidableEq\left(I\right)] \forall (U:unitaryGroup\left(I, \mathbb{C}\right)), \forall (v:I\to \mathbb{C}), (dotProduct\left(star\left(v\right), v\right)=1)\Rightarrow dotProduct\left(star\left(Matrix.mulVec\left(val\left(U\right), v\right)\right), Matrix.mulVec\left(val\left(U\right), v\right)\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.unitary_vector_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex dot product of the pointwise conjugate vector with the vector equals one. Coercion from unitaryGroup gives its matrix. This previously local helper is shared by the qutrit and quadbit attainment proofs.

**Theorem 1.5 (A normalized outer product is idempotent).**

$$\forall (I:Type), [Fintype\left(I\right)] \forall (v:I\to \mathbb{C}), (dotProduct\left(star\left(v\right), v\right)=1)\Rightarrow Matrix.vecMulVec\left(v, star\left(v\right)\right)\cdot Matrix.vecMulVec\left(v, star\left(v\right)\right)=Matrix.vecMulVec\left(v, star\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.pure_outer_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized complex vector determines an idempotent rank-one outer product on any finite index type. This is the original local proof exposed for reuse in the quadbit purity computation.

**Theorem 1.6 (Normalized-vector attainment).**

$$\forall (n:\mathbb{N}), \forall (v:(Fin\left(3\right)\times Fin\left(n\right))\to \mathbb{C}), (\sum_{ij:(Fin\left(3\right)\times Fin\left(n\right))} star\left(v\left(ij\right)\right)\cdot v\left(ij\right)=1)\Rightarrow (APPT\left(rhoPure\left(n, v\right)\right))\land (Matrix.PosSemidef\left(rhoPure\left(n, v\right)\right))\land (Matrix.trace\left(rhoPure\left(n, v\right)\right)=1)\land (Matrix.trace\left(rhoPure\left(n, v\right)\cdot rhoPure\left(n, v\right)\right)=Complex.ofReal\left(\frac{3\cdot (n:\mathbb{R})+8}{(3\cdot (n:\mathbb{R})+2)^{2}}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.pure_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalization hypothesis is a complex equality. An explicit antisymmetric Gram complement makes the partial transpose positive under every global unitary; the normalized perturbation is positive, has trace one, and has the displayed complex trace-square.

**Theorem 1.7 (Rank-n projector attainment).**

$$\forall (n:\mathbb{N}), (0<n)\Rightarrow \forall (P:Matrix\left((Fin\left(3\right)\times Fin\left(n\right)), (Fin\left(3\right)\times Fin\left(n\right)), \mathbb{C}\right)), ((Matrix.IsHermitian\left(P\right))\land (P\cdot P=P)\land (Matrix.rank\left(P\right)=n))\Rightarrow (APPT\left(rhoProjector\left(n, P\right)\right))\land (Matrix.PosSemidef\left(rhoProjector\left(n, P\right)\right))\land (Matrix.trace\left(rhoProjector\left(n, P\right)\right)=1)\land (Matrix.trace\left(rhoProjector\left(n, P\right)\cdot rhoProjector\left(n, P\right)\right)=Complex.ofReal\left(\frac{3}{8\cdot (n:\mathbb{R})}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.projector_attainment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive n, a Hermitian idempotent of rank n produces a density matrix of purity 3/(8n). The proof constructs a positive qutrit Kraus decomposition after conjugation and takes the full transpose to obtain the second-factor convention.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.conjugate_outer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.projector_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.pure_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.pure_outer_square`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.rhoProjector`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.rhoPure`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QutritPerturbationAttainment.unitary_vector_norm`
- Dependency: [D5/S3/Quantum/Dynamics/KickedIsingNegativityRefutation](../../Dynamics/KickedIsingNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtCorner](UniformSchmidtCorner.md)
