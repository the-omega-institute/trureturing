# Common hyperplane cuts and embedding constraint rigidity

## Abstract

Common hyperplane cuts and embedding constraint rigidity

For the next statement K is a field, E a finite-dimensional K-vector space, I any index type, V(i) a K-subspace of E, phi a K-linear functional and s a finite subset of I. Write S(V,A) for the supremum of V(i) over i in A, T(V,phi,A) for the supremum of V(i) intersect ker(phi) over i in A, and C(V,P) for the sum over B in P.parts of dim_K S(V,B) minus one. Finpartition(s) means a finite partition of s into nonempty disjoint blocks; the empty s has the empty partition. GP(V,phi,s) means both: no V(i), for i in s, is contained in ker(phi); and for all finite A,B,C contained in s, if (T(V,phi,A)+S(V,B)) intersect (T(V,phi,A)+S(V,C)) is contained in ker(phi), then that intersection equals T(V,phi,A). The middle family A may be empty, as in the footnote to Definition 5.1 and the base case of Lemma 5.3.

**Theorem 1.1 (An attaining partition for a hyperplane in general position).**

$$\forall K \in Type*,\; \forall E \in Type*,\; \forall I \in Type*,\; [Field\left(K\right)], [AddCommGroup\left(E\right)], [Module\left(K, E\right)], [FiniteDimensional\left(K, E\right)], \forall V \in I \to Submodule\left(K, E\right),\; \forall phi \in LinearMap\left(K, E, K\right),\; \forall s \in Finset\left(I\right),\; GP\left(V, phi, s\right) \Rightarrow \left(\exists P \in Finpartition\left(s\right),\; dim\left(K, T\left(V, phi, s\right)\right) = C\left(V, P\right) \land \left(\forall Q \in Finpartition\left(s\right),\; dim\left(K, T\left(V, phi, s\right)\right) \le C\left(V, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ActualWindowCommonKernel.hyperplane_partition_rank` (`✓ std3`). ∎

*Citation.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

This is the deterministic implication of Raz and Wigderson, Theorem 5.2. Let T be the total cut span and group i and j when T+V(i)=T+V(j). Each such extension has dimension dim(T)+1. Distinct extensions therefore intersect precisely in T. For a union A of intervening classes, the general-position intersection law applied to T(A)+S(B) and T(A)+S(C) removes every dependence between the first and last classes modulo T(A). Induction gives supremum independence of all class cut spans. If there is only one class, the entire uncut span has dimension dim(T)+1 and the one-block partition is tight. Otherwise every class is a proper subfamily; recursively choose tight partitions there and combine them by Finpartition.bind. This constructs a partition whose cost is exactly the cut rank. The opposite inequality follows by bounding each block cut inside its uncut span intersect ker(phi).

The new recursive partition construction and its independence argument are the necessary non-normalization steps. The one-dimensional extension calculations, finite-sup dimension identities and finite-partition constructors reuse pinned Mathlib. No claim of mathematical novelty is made for the classical theorem. The result is a necessary intermediate for R5 (31.7), not the complete generic rank or (31.10).

For the block statement, B is a finite block type and J assigns a finite coordinate type J(i) to each i in B. BlockSpace(K,B,J) is the dependent product of J(i) to K. An array b has type (i in B) to (I to J(i) to K). The row blockRows(b,sigma,i) places b(i,sigma) in coordinate block i and is zero elsewhere. BF(b)(sigma) is the span of all these block-supported rows. Write q(b,A,i) for dim_K span of b(i,sigma) over sigma in A, BC(b,P) for the sum over A in P.parts of (sum over i in B of q(b,A,i)) minus one, and R(b,phi,k,s) for the dimension of the span of all rows phi(blockRows(b,sigma,k)) times blockRows(b,sigma,i) minus phi(blockRows(b,sigma,i)) times blockRows(b,sigma,k), with sigma in s and i in B. In this definition the SAME phi and k are used in every row; the i=k row is zero.

**Theorem 1.2 (The common-constraint block row partition formula).**

$$\forall K \in Type*,\; \forall I \in Type*,\; \forall B \in Type*,\; \forall J \in B \to Type*,\; [Field\left(K\right)], [Fintype\left(B\right)], [\forall i \in B,\; Fintype\left(J\left(i\right)\right)], \forall b \in \left(\forall i \in B,\; I \to J\left(i\right) \to K\right),\; \forall phi \in LinearMap\left(K, BlockSpace\left(K, B, J\right), K\right),\; \forall k \in B,\; \forall s \in Finset\left(I\right),\; \left(\forall sigma \in I,\; sigma \in s \Rightarrow phi\left(blockRows\left(b, sigma, k\right)\right) \ne 0\right) \Rightarrow \left(GP\left(BF\left(b\right), phi, s\right) \Rightarrow \left(\exists P \in Finpartition\left(s\right),\; R\left(b, phi, k, s\right) = BC\left(b, P\right) \land \left(\forall Q \in Finpartition\left(s\right),\; R\left(b, phi, k, s\right) \le BC\left(b, Q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ActualWindowCommonKernel.block_common_rows_partition_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

The common rows for a fixed sigma span BF(b)(sigma) intersect ker(phi): the linear map v to phi(blockRows(b,sigma,k))v minus phi(v)blockRows(b,sigma,k) maps the uncut span onto that intersection whenever its distinguished coefficient is nonzero. The span of the uncut subspaces for A is the product, over coordinate blocks i, of span(b(i,sigma): sigma in A). Thus its dimension is the sum of q(b,A,i). Substituting these actual row spaces into the attaining-partition theorem gives the displayed equality and every partition upper bound. The embedding-kernel rigidity theorem below uses both the attaining partition and these universal partition bounds.

For R5 (31.5)-(31.7), take the scalar field to be the fraction field K(z) over the normal closure K, I to be the embedding type Omega, B to be the window indices, J(i) to index the chosen basis of X(i), and b(i,sigma)(j)=sigma(x(i,j)) after scalar extension. Take s to be all embeddings, k the first window and phi(v)=sum over i,j of z(i,j)v(i,j). Then phi(blockRows(b,sigma,i)) is U(i,sigma), and the displayed rows are exactly U(1,sigma) times the i-th block row minus U(i,sigma) times the first block row. SymbolicHyperplaneGeneralPosition.symbolic_general_position proves both clauses of this GP premise for scalar extensions of constant subspaces and independent symbolic normal coordinates, including empty and overlapping subfamilies. Its symbolic_block_common_rows_partition_rank consumes that proof and proves the distinguished symbolic coefficient nonzero from a nonzero base row, yielding this common-row partition formula without a GP premise. The new proof uses directional derivations of the rational function field; individual nonvanishing by itself would not discharge the intersection clause. The unique fewest-block optimum, Galois invariance, descent inside the original ratio field, the rank of the original polynomial matrix, a nonzero original-coefficient minor, and original-F specialization remain outside these statements. No maximizing field or original-label tuple is produced here.

For the rigidity statement, F and D are fields, D and K are F-algebras, emb is a finite family of F-algebra embeddings D to K, X(i) is an F-subspace of D, and x(i) is an F-basis of X(i) indexed by J(i). Set ER(emb,X,x)(i,sigma,j)=emb(sigma)(x(i,j)). CoefficientSpace(K,B,J) is the space of K-valued functions on the pairs (i,j). A coefficient tuple z is indexed by those pairs; M is the sum of the cardinalities of J(i). Let N(z)(v)=sum over (i,j) of v(i,j)z(i,j). CM(b,phi,k) has rows indexed by (sigma,i) and columns by (j,l); its row is the flattened vector phi(blockRows(b,sigma,k)) blockRows(b,sigma,i) minus phi(blockRows(b,sigma,i)) blockRows(b,sigma,k). Ker(CM) means the kernel of its multiplication map on coefficient columns. Line(K,z) is the K-linear span of z. Write GPall(b,N(z)) for GP(BF(b),N(z),univ), NZall(b,N(z),k) for nonvanishing of every distinguished coefficient, and BC(b,P) for the partition cost already defined.

**Theorem 1.3 (Rigidity of the actual simultaneous embedding constraints).**

$$\forall F \in Type*,\; \forall D \in Type*,\; \forall K \in Type*,\; \forall I \in Type*,\; \forall B \in Type*,\; \forall J \in B \to Type*,\; [Field\left(F\right)], [Field\left(D\right)], [Field\left(K\right)], [Algebra\left(F, D\right)], [Algebra\left(F, K\right)], [Fintype\left(I\right)], [Fintype\left(B\right)], [\forall i \in B,\; Fintype\left(J\left(i\right)\right)], \forall emb \in I \to AlgHom\left(F, D, K\right),\; \forall X \in B \to Submodule\left(F, D\right),\; \forall x \in \left(\forall i \in B,\; Basis\left(J\left(i\right), F, X\left(i\right)\right)\right),\; \forall z \in CoefficientSpace\left(K, B, J\right),\; \forall k \in B,\; z \ne 0 \Rightarrow \left(NZall\left(ER\left(emb, X, x\right), N\left(z\right), k\right) \Rightarrow \left(GPall\left(ER\left(emb, X, x\right), N\left(z\right)\right) \Rightarrow \left(Ker\left(CM\left(ER\left(emb, X, x\right), N\left(z\right), k\right)\right) = Line\left(K, z\right) \Leftrightarrow \left(\forall P \in Finpartition\left(univ\left(I\right)\right),\; M-1 \le BC\left(ER\left(emb, X, x\right), P\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ActualWindowCommonKernel.embedding_common_kernel_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Orit E. Raz; Avi Wigderson (2019). *Subspace arrangements, graph rigidity and derandomization through submodular optimization*. URL: <https://arxiv.org/abs/1901.09423v1>.

*Commentary.*

The matrix here acts on an actual coefficient column c. At (sigma,i) its value is U(k,sigma) times sum over j of emb(sigma)(x(i,j))c(i,j), minus U(i,sigma) times sum over j of emb(sigma)(x(k,j))c(k,j). Hence its kernel is the simultaneous embedding-coordinate version of the common constraint, rather than just an abstract cut span. The same z is in this kernel, since the two products U(k,sigma)U(i,sigma) cancel. Flattening dependent coordinate blocks is a linear equivalence; pinned Mathlib row-rank equality identifies the matrix rank with the common-row span rank. Rank-nullity and the nonzero kernel vector z show that the kernel has dimension at least one. If the kernel is Line(K,z), its dimension is one, and each partition bound forces cost at least M-1. Conversely, applying the lower threshold to the attaining partition forces the kernel dimension to be one. The inclusion Line(K,z) in the kernel is then equality. Thus all simultaneous coefficient solutions are scalar multiples of this same tuple exactly under the stated partition criterion.

For the source correspondence, take K=K_0(z) with K_0 the normal closure, emb the complete family Hom_F(D,K_0) followed by scalar inclusion, X and x the normalized windows and bases of (31.5), and k=1. This theorem is a conditional rigidity consequence of (31.5)-(31.7) for the scalar-extended embedding-coordinate constraint. Its premises are the explicit general-position law, nonzero distinguished coefficients, and a nonzero common coefficient tuple. It assumes neither a rank formula nor genericity, field descent, original-F specialization, or (31.10). The symbolic general-position and distinguished-coefficient hypotheses are discharged for constant rows in SymbolicHyperplaneGeneralPosition. Establishing the original h-1 row basis and the actual embedding dimension and distinctness identifications, transferring the embedding output coordinates to the original polynomial map, Galois descent, and returning an original-F attaining tuple remain separate obligations. Registration for these public targets is unfinished; no declared_validated status is asserted.

## References

- Truth anchor: `D5/S3/Factorization/Galois/ActualWindowCommonKernel.block_common_rows_partition_rank`
- Truth anchor: `D5/S3/Factorization/Galois/ActualWindowCommonKernel.embedding_common_kernel_rigidity`
- Truth anchor: `D5/S3/Factorization/Galois/ActualWindowCommonKernel.hyperplane_partition_rank`
- Dependency: [D5/S3/Combinatorics/SubspaceCodes/MRDDensityColumnTensor](../../Combinatorics/SubspaceCodes/MRDDensityColumnTensor.md)
