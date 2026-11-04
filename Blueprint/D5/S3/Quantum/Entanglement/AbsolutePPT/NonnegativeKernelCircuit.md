# Circuits of a finite nonnegative kernel

## Abstract

Finite kernels over any ordered field admit independent sign-conformal decompositions into globally support-minimal circuits, with support and nullity bounds.

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

**Definition 1.7 (Finite support over a field).**

$$\forall (F:Type), [Field\left(F\right)] [LinearOrder\left(F\right)] \forall (E:Type), [Fintype\left(E\right)] \forall (v:E\to F), support\left(v\right)=\{ i:E\mid v\left(i\right)\neq 0\}$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.support` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite support records exactly the nonzero coordinates. Its scalar field and finite label type have independent universes. The conic compression proof uses its cardinality.

**Theorem 1.8 (A global circuit retaining a prescribed coordinate).**

$$\forall (F:Type), [Field\left(F\right)] [LinearOrder\left(F\right)] [IsStrictOrderedRing\left(F\right)] \forall (E:Type), [Fintype\left(E\right)] \forall (m:\mathbb{N}), \forall (A:Fin\left(m\right)\to E\to F), \forall (x:E\to F), \forall (e:E), ((mulVec\left(A, x\right)=0)\land (x\left(e\right)\neq 0))\Rightarrow \exists (c:E\to F), (mulVec\left(A, c\right)=0)\land ((c\left(e\right)\neq 0)\land ((\forall (i:E), (c\left(i\right)=0)\lor sign\left(c\left(i\right)\right)=sign\left(x\left(i\right)\right))\land (\forall (w:E\to F), ((mulVec\left(A, w\right)=0)\land ((w\neq 0)\land (supp\left(w\right)\subseteq supp\left(c\right))))\Rightarrow supp\left(w\right)=supp\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.signConformalGlobalKernelCircuit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar field F and finite label type E have independent universes. The only scalar instances are Field F, LinearOrder F and IsStrictOrderedRing F. The matrix has any natural row count m. The notation supp denotes Function.support. Every nonzero signed kernel vector supported in the output has exactly that support: competitors have no sign restriction and need not be nonzero at e. Zero rows, repeated or zero columns and non-Archimedean ordered fields are included.

Normalize the input orthant by signs ±1. The negative signed e-column is a nonnegative combination of the other original columns. Minimize support among nonnegative representations of this same point p, permitting p = 0 and empty support. An active signed dependence, oriented to have a positive coordinate, permits minimum-ratio subtraction that preserves p and nonnegativity while erasing an active coordinate. The contradiction proves independence of the compressed active columns. Restore coefficient one at e. For every signed supported kernel d, subtract d e times this normalized relation. The residual vanishes at e and on its independent remaining columns, so d is a scalar multiple of the relation. Nonzero d has a nonzero scalar and equal support. Undo the orthant signs. The same-p feasibility and strict erasure is the new reusable inference in this proof; sign transport and finite-sum normalization alone do not supply it. The finite minimum-ratio proof is shared with the original Real API, whose statements and cofactor consumers are preserved. This is the classical elementary-vector method, without a claim of mathematical novelty.

**Theorem 1.9 (An independent conformal circuit decomposition).**

$$\forall (F:Type), [Field\left(F\right)] [LinearOrder\left(F\right)] [IsStrictOrderedRing\left(F\right)] \forall (E:Type), [Fintype\left(E\right)] \forall (m:\mathbb{N}), \forall (A:Fin\left(m\right)\to E\to F), \forall (x:E\to F), (mulVec\left(A, x\right)=0)\Rightarrow \exists (n:\mathbb{N}), \exists (c:Fin\left(n\right)\to E\to F), (\sum_{j:Fin\left(n\right)} c\left(j\right)=x)\land ((LinearIndependent\left(F, c\right))\land ((n\leq card\left(support\left(x\right)\right))\land ((n\leq finrank\left(F, ker\left(mulVecLin\left(A\right)\right)\right))\land (\forall (j:Fin\left(n\right)), (c\left(j\right)\neq 0)\land ((mulVec\left(A, c\left(j\right)\right)=0)\land ((\forall (i:E), (c\left(j, i\right)=0)\lor sign\left(c\left(j, i\right)\right)=sign\left(x\left(i\right)\right))\land (\forall (w:E\to F), ((mulVec\left(A, w\right)=0)\land ((w\neq 0)\land (supp\left(w\right)\subseteq supp\left(c\left(j\right)\right))))\Rightarrow supp\left(w\right)=supp\left(c\left(j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.signConformalGlobalKernelCircuitDecomposition` (`✓ std3`). ∎

*Citation.* Stefan Mueller and Georg Regensburger (2016). *Elementary vectors and conformal sums in polyhedral geometry and their relevance for metabolic pathway analysis*. URL: <https://arxiv.org/abs/1512.00267v2>.

*Commentary.*

For every kernel vector x there is a finite family c indexed by Fin n whose sum is x. The family is linearly independent over F. Its size is bounded by both the number of nonzero coordinates of x and the dimension over F of the kernel of mulVecLin A. Each summand is nonzero, belongs to the same kernel and is sign-conformal to x. Each is globally support-minimal: every nonzero signed kernel competitor supported within that summand has exactly the same support, without a sign condition on the competitor. Positive scalars have been absorbed into the summands. The scalar and label universes are independent, and the only scalar instances are Field, LinearOrder and IsStrictOrderedRing.

Apply the prescribed-coordinate circuit theorem to a nonzero residual. The original finite minimum-ratio subtraction, applied to absolute coordinate values, produces a positive multiple of this circuit and a residual in the same orthant with strictly smaller support. The selected boundary coordinate is nonzero in the new summand and zero in the residual. All circuits subsequently extracted from the residual vanish at that coordinate. This one-sided pivot puts the new summand outside their span, so adjoining it preserves independence. Induction terminates with the zero residual. Independence inside the kernel gives the nullity bound. This is the classical elementary-vector conformal-sum result of Mueller and Regensburger, Theorem 3, with the finite ordered-field argument made explicit; no mathematical novelty is asserted. Zero is represented by n = 0. Empty labels, zero rows, arbitrary rank, zero or repeated columns and non-Archimedean ordered fields remain included.

A box-fiber optimization application uses the same ordered field F and an arbitrary linear objective L : (E → F) →ₗ[F] F. Fix A, a right-hand side b, lower and upper coordinate bounds l,u and actual feasible vectors x,y satisfying A x = b = A y and l ≤ x,y ≤ u. For minimization assume L y < L x. Decompose the actual displacement d = y - x. Linearity makes the sum of the objective changes L(c j) strictly negative, so at least one summand has negative change. For each coordinate, all summands have the sign of d there and their sum is d. Hence each summand lies between 0 and d in the appropriate order, and x + c j lies on the coordinatewise interval between x and y, inside the same box. It also remains in the same fiber. This produces an improving nonzero global circuit displacement feasible at x, without assuming such a circuit as input. Conversely, any such displacement is an improving feasible point. Thus x is optimal among this box fiber exactly when no feasible nonzero global circuit displacement improves L. This is an existence criterion over a field, not an integer augmentation algorithm, an iteration bound or a claim that the entire family can be added in arbitrary order.

For arbitrary q : E → (Fin d → F), take the homogeneous matrix A with d + 1 rows, first row identically 1 and remaining rows q. The kernel equations are exactly sum x i = 0 and sum x i • q i = 0. Substituting this matrix yields an independent conformal sum of globally minimal affine relations with the same support and kernel-dimension bounds. Both original affine equations hold for every summand, and every signed affine relation supported in a summand has equal support. Original labels are retained even when q has coincident values; d = 0 and empty label types are allowed. The optimization application applies to coefficient boxes in this same affine fiber. No passage to an injective point set, normalized list or separately supplied realization is required.

For arbitrary same-field points q : E → (Fin d → F), an affine relation x with sum x i = 0, sum x i • q i = 0 and x e ≠ 0 gives the application A r i = (1, q i) r with d + 1 homogeneous rows. The output c satisfies both affine equations, retains e, and has its positive labels contained in the positive labels of x and its negative labels contained in the negative labels of x. Every nonzero signed affine competitor supported in c has equal support, including competitors zero at e. The positive coefficient sum is strictly positive, and the negative coefficient sum is its opposite. Delete the zero coefficients, normalize the two sides and use their zero vector sum: both center masses equal one point p. Thus p lies in the convex hull of each strict sign side of c and, by containment, in each corresponding strict sign-side hull of x. The construction keeps the original labels, permits repeated points and d = 0, and uses no Archimedean assumption. This complete universally parameterized application is checked transiently; no separate thin Radon theorem is retained.

For a system of three homogeneous inequalities on nonnegative variables, append three nonnegative slack coordinates and use the augmented matrix with a negative identity block. Its nonnegative kernel projects onto the original feasible cone, and each circuit projects to a feasible vector supported on at most four original coordinates. This supplies a general reduction for the three-row spectral relaxation. Identifying the resulting small-support spectral cases and obtaining a final APPT purity bound require further arguments.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.Circuit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.InKernel`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_deleted_cols_linearIndependent`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.circuit_support_card_le`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nonnegKernel_mem_hull_circuit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.nzSupport`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.signConformalGlobalKernelCircuit`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.signConformalGlobalKernelCircuitDecomposition`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit.support`
