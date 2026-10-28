# Circuits of a finite nonnegative kernel

## Abstract

A nonnegative solution of finitely many homogeneous real equations decomposes into support-minimal solutions, each using at most one more coordinate than equations.

**Definition 1.1 (Nonzero support).**

$$\forall (J:Type), [Fintype\left(J\right)] \forall (v:J\to \mathbb{R}), nzSupport\left(v\right)=\{ j:J\mid v\left(j\right)\neq 0\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nzSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The support consists of the coordinates at which the vector is nonzero. It is a finite set for every finite coordinate type, including the empty type.

**Definition 1.2 (Nonnegative homogeneous solutions).**

$$\forall (J:Type), [Fintype\left(J\right)] \forall (m:\mathbb{N}), \forall (B:Fin\left(m\right)\to J\to \mathbb{R}), \forall (v:J\to \mathbb{R}), InKernel\left(B, v\right)\iff (\forall (j:J), 0\leq v\left(j\right))\land (\forall (r:Fin\left(m\right)), \sum_{j:J} B\left(r, j\right)\cdot v\left(j\right)=0)$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.InKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matrix has an arbitrary natural number of rows and an arbitrary finite coordinate type. A feasible vector is coordinatewise nonnegative and has zero scalar product with every row. No rank, nonzero-column or nonempty-type hypothesis is imposed.

**Definition 1.3 (Support-minimal solutions).**

$$\forall (J:Type), [Fintype\left(J\right)] \forall (m:\mathbb{N}), \forall (B:Fin\left(m\right)\to J\to \mathbb{R}), \forall (v:J\to \mathbb{R}), Circuit\left(B, v\right)\iff (InKernel\left(B, v\right))\land ((v\neq 0)\land (\forall (w:J\to \mathbb{R}), ((InKernel\left(B, w\right))\land ((w\neq 0)\land (nzSupport\left(w\right)\subseteq nzSupport\left(v\right))))\Rightarrow card\left(nzSupport\left(v\right)\right)\leq card\left(nzSupport\left(w\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.Circuit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A circuit is a nonzero feasible vector whose support cardinality is minimal among the nonzero feasible vectors with support contained in its support. Scaling is not normalized, so all positive multiples of a circuit are permitted.

**Theorem 1.4 (Conic decomposition).**

$$\forall (J:Type), [Fintype\left(J\right)] \forall (m:\mathbb{N}), \forall (B:Fin\left(m\right)\to J\to \mathbb{R}), \forall (x:J\to \mathbb{R}), (InKernel\left(B, x\right))\Rightarrow x\in hull\left(\mathbb{R}, \{ v:J\to \mathbb{R}\mid Circuit\left(B, v\right)\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nonnegKernel_mem_hull_circuit` (`✓ std3`). ∎

*Citation.* Stefan Mueller and Georg Regensburger (2016). *Elementary vectors and conformal sums in polyhedral geometry and their relevance for metabolic pathway analysis*. URL: <https://arxiv.org/abs/1512.00267v2>.

*Commentary.*

Every feasible vector belongs to the pointed conic hull of the circuits. This is the fully nonnegative specialization of the subspace-cone decomposition in Mueller and Regensburger, Theorem 3. Membership has its usual finite meaning: there is a finitely supported family of nonnegative real coefficients on circuits whose weighted sum is exactly the input. Zero is the empty combination. For a nonzero input, choose a feasible vector of minimum support within its support. Subtract the largest permitted positive multiple, determined by the minimum positive coordinate ratio. A coordinate vanishes, the residual stays feasible, and induction on support cardinality finishes the decomposition.

**Theorem 1.5 (Independent columns after deleting a supported coordinate).**

$$Circuit\left(B, v\right) \Rightarrow LinearIndependent\left(supportedColumnsAfterDeleting\left(B, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_deleted_cols_linearIndependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compiled declaration retains arbitrary finite J with its Fintype instance, arbitrary m, the full matrix B and vector v, the Circuit witness, the supported deleted coordinate i and its support proof. For any supported coordinate of a circuit, the other supported columns are linearly independent. A dependence among them gives a signed kernel direction vanishing at the deleted coordinate. Orient it to have a positive entry and use the existing minimum-ratio subtraction. The deleted coordinate stays positive while another supported coordinate vanishes, contradicting support minimality. This is the classical finite-dimensional elementary-vector argument; it does not assume a cardinality bound. The support bound now follows by the dimension inequality, and the cofactor completeness theorem uses the same independence result to select a nonzero minor.

**Theorem 1.6 (Support bound).**

$$\forall (J:Type), [Fintype\left(J\right)] \forall (m:\mathbb{N}), \forall (B:Fin\left(m\right)\to J\to \mathbb{R}), \forall (v:J\to \mathbb{R}), (Circuit\left(B, v\right))\Rightarrow card\left(nzSupport\left(v\right)\right)\leq m+1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_support_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A circuit has support cardinality at most the number of rows plus one. Delete one supported coordinate, apply deleted-column independence, and bound the size of that independent family by the dimension of the row-coordinate space. The deleted-column theorem contains the minimum-ratio contradiction once. Every denominator in that argument is positive where used. The statement includes zero rows, dependent rows, zero columns and zero coordinates; with no rows, circuits have at most one supported coordinate.

For a system of three homogeneous inequalities on nonnegative variables, append three nonnegative slack coordinates and use the augmented matrix with a negative identity block. Its nonnegative kernel projects onto the original feasible cone, and each circuit projects to a feasible vector supported on at most four original coordinates. This supplies a general reduction for the three-row spectral relaxation. Identifying the resulting small-support spectral cases and obtaining a final APPT purity bound require further arguments.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.Circuit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.InKernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_deleted_cols_linearIndependent`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_support_card_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nonnegKernel_mem_hull_circuit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nzSupport`
