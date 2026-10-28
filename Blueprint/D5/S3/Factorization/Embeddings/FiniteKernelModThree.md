# Finite-kernel descent for cube classes

## Abstract

Finite kernels preserve the original quotient by triples and bound embedded unit cube classes.

Let A and L be additive commutative groups and f:A->L a surjective homomorphism with finite kernel. Assume 3a=0 implies a=0 for every a in A. ModN(A,3) is Mathlib's quotient A/3A, with its standard ZMod(3) module structure. Multiplication by three is injective on the finite kernel, hence surjective there. If f(a)=3l, lift l to v and solve 3t=a-3v inside the kernel. Then a=3(v+t) inside A. Thus the induced map A/3A -> L/3L is an equivalence. For finite free L, Mathlib's ModN.basis supplies all coordinate reduction.

**Theorem 1.1 (Finite free image determines the cube quotient dimension).**

$$\forall A \in AddCommGroup,\; \forall L \in AddCommGroup,\; \forall f \in \operatorname{AddHom}\left(A, L\right),\; \operatorname{FiniteKernelDescentHypotheses}\left(A, L, f\right) \Rightarrow \left(\operatorname{ModuleFinite}\left(\operatorname{ZMod}\left(3\right), \operatorname{ModN}\left(A, 3\right)\right) \land \operatorname{finrank}\left(\operatorname{ZMod}\left(3\right), \operatorname{ModN}\left(A, 3\right)\right) = \operatorname{finrank}\left(Int, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/FiniteKernelModThree.modThree_finite_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

FiniteKernelDescentHypotheses denotes exactly the preceding group, surjectivity, finite-kernel and no-three-torsion hypotheses, together with L finite free over Int. The equivalence transfers finite dimensionality and the reduced integral basis computes the dimension.

**Theorem 1.2 (Original unit cube quotients satisfy the Dirichlet bound).**

$$\forall K \in NumberField,\; \forall U \in CommGroup,\; \forall i \in \operatorname{MonoidHom}\left(U, \operatorname{Units}\left(\operatorname{Integers}\left(K\right)\right)\right),\; \operatorname{EmbeddedUnitHypotheses}\left(K, U, i\right) \Rightarrow \left(\operatorname{ModuleFinite}\left(\operatorname{ZMod}\left(3\right), \operatorname{ModN}\left(\operatorname{Additive}\left(U\right), 3\right)\right) \land \operatorname{finrank}\left(\operatorname{ZMod}\left(3\right), \operatorname{ModN}\left(\operatorname{Additive}\left(U\right), 3\right)\right) \le \operatorname{UnitRank}\left(K\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Embeddings/FiniteKernelModThree.embedded_units_modThree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here K is any number field, U any commutative group, i:U->Units(O(K)) injective, and u^3=1 implies u=1 in U. These are all the EmbeddedUnitHypotheses. DirichletUnitCompletion splits integer units into finite torsion and a free lattice. Restrict the free coordinate to its actual image L. Its kernel injects into the finite torsion group; L is a finite free integral submodule. Finite-kernel descent then bounds the dimension by the ambient Dirichlet rank. An embedding of groups alone does not imply an embedding of cube quotients: the inclusion 3Int->Int sends a nonzero cube class to zero. The kernel correction supplies cube witnesses in U itself. The consumed helper exists_original_cube_of_quotient_eq takes equality of two classes in ModN(Additive(U),3) and returns w in the same U with u=v*w^3. ResetQ4UnitCubes uses it for both original-order normal forms; it is quotient-kernel witness extraction, not a separate content result.

## References

- Truth anchor: `D5/S3/Factorization/Embeddings/FiniteKernelModThree.embedded_units_modThree`
- Truth anchor: `D5/S3/Factorization/Embeddings/FiniteKernelModThree.modThree_finite_finrank`
- Dependency: [D5/S3/Factorization/Embeddings/DirichletUnitCompletion](DirichletUnitCompletion.md)
