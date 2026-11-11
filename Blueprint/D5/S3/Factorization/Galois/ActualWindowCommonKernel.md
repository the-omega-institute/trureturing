# Common kernels and original window labels

## Abstract

Common kernels and original window labels

Let F be a field and L an extension field of finite dimension over F. Let T be a finite index type with a distinguished index k, and let W assign an F-linear subspace of L to each index. Sections(W) denotes the dependent product of the subspaces W(i); vectors in a section are viewed as elements of L. For nonzero labels r(i), J(W,r) is the intersection of the actual scaled subspaces r(i)W(i). Equivalently, x belongs to J(W,r) exactly when the product of the inverse of r(i) and x belongs to W(i) for every i. Write d(W,r) for its F-dimension, and M(W) for the sum of the F-dimensions of the windows.

For a tuple p, C(W,k,p) sends a section v to the tuple whose i-th coordinate is p(k)v(i) minus p(i)v(k). Its k-th output coordinate is zero. Write R(W,k,p) for the F-dimension of its range, and ratio(k,p)(i) for p(k)/p(i). All these objects lie in the given extension field.

**Theorem 1.1 (Common kernel rank and positive intersection).**

$$\forall F \in Type*,\; \forall L \in Type*,\; \forall T \in Type*,\; [Field\left(F\right)], [Field\left(L\right)], [Algebra\left(F, L\right)], [Fintype\left(T\right)], [FiniteDimensional\left(F, L\right)], \forall W \in T \to Submodule\left(F, L\right),\; \forall k \in T,\; \forall p \in Sections\left(W\right),\; \left(\forall i \in T,\; p\left(i\right) \ne 0\right) \Rightarrow \left(R\left(W, k, p\right)+d\left(W, ratio\left(k, p\right)\right) = M\left(W\right) \land 0 < d\left(W, ratio\left(k, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ActualWindowCommonKernel.common_kernel_rank_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projection of a kernel vector to coordinate k is an F-linear equivalence onto J(W,ratio(k,p)). The inverse reconstructs every coordinate as p(i)/p(k) times that one vector. Thus all window conditions constrain the same vector. Rank-nullity gives the displayed equality, and p(k) is a nonzero element of the intersection. A singleton index type gives the zero constraint and the original window.

**Theorem 1.2 (Simultaneous original-label attainment).**

$$\forall F \in Type*,\; \forall L \in Type*,\; \forall T \in Type*,\; [Field\left(F\right)], [Field\left(L\right)], [Algebra\left(F, L\right)], [Finite\left(T\right)], [FiniteDimensional\left(F, L\right)], \forall W \in T \to Submodule\left(F, L\right),\; \forall k \in T,\; \left(\forall i \in T,\; W\left(i\right) \ne \operatorname{Bot}.\operatorname{bot}\right) \Rightarrow \left(\exists p \in Sections\left(W\right),\; \left(\forall i \in T,\; p\left(i\right) \ne 0\right) \land \left(\left(\forall q \in Sections\left(W\right),\; \left(\forall i \in T,\; q\left(i\right) \ne 0\right) \Rightarrow R\left(W, k, q\right) \le R\left(W, k, p\right)\right) \land \left(\forall r \in T \to L,\; \left(\forall i \in T,\; r\left(i\right) \ne 0\right) \Rightarrow \left(r\left(k\right) = 1 \Rightarrow \left(0 < d\left(W, r\right) \Rightarrow d\left(W, ratio\left(k, p\right)\right) \le d\left(W, r\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/ActualWindowCommonKernel.exists_joint_rank_minimizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose the least intersection dimension among tuples with every coordinate nonzero. Any positive original-label intersection contains a nonzero vector w; the section with coordinate r(i) inverse times w belongs to the original windows, has no zero coordinates, and reconstructs precisely those labels when r(k) is one. This supplies the full comparison with original labels. The common-kernel rank identity then shows that the same chosen tuple maximizes constraint rank. The argument works in any characteristic and for independently scaled windows. The rank optimum over actual tuples alone does not identify an intermediate field or give a subfield dimension formula.

## References

- Truth anchor: `D5/S3/Factorization/Galois/ActualWindowCommonKernel.common_kernel_rank_identity`
- Truth anchor: `D5/S3/Factorization/Galois/ActualWindowCommonKernel.exists_joint_rank_minimizer`
