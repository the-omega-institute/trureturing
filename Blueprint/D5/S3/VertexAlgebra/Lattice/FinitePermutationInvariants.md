# Invariants of a finite permutation basis

## Abstract

A representation permuting a finite basis has one invariant dimension per actual basis orbit.

Let a group act on a finite index set, and let a linear representation permute a basis according to that action. Fixed vectors correspond exactly to scalar functions on the orbit quotient. Here K,G,X,V are types; V is a K-module, b is an X-indexed basis, and rho is a monoid homomorphism from G to its K-linear automorphisms satisfying rho(g)(b(x))=b(g smul x) for every g and x. Orbits(G,X) denotes the quotient by the actual orbit relation, Fun(Q,K) the scalar function space, and Fixed(rho) the submodule of vectors fixed by every group element. The acting group need not be finite, stabilizers may be nontrivial, and the field may have arbitrary characteristic.

**Definition 1.1 (Fixed vectors and orbit coefficients).**

$$\forall K,G,X,V, \operatorname{Field}\left(K\right) \land \operatorname{Group}\left(G\right) \land \operatorname{MulAction}\left(G, X\right) \land \operatorname{Fintype}\left(X\right) \land \operatorname{AddCommGroup}\left(V\right) \land \operatorname{Module}\left(K, V\right) \Rightarrow \forall rho\in \operatorname{MonoidHom}\left(G, \operatorname{LinearAut}\left(K, V\right)\right), \forall b\in \operatorname{Basis}\left(X, K, V\right), (\forall g\in G, \forall x\in X, \operatorname{rho}\left(g, \operatorname{b}\left(x\right)\right)=\operatorname{b}\left(\operatorname{smul}\left(g, x\right)\right)) \Rightarrow \operatorname{LinearEquiv}\left(K, \operatorname{Fixed}\left(rho\right), \operatorname{Fun}\left(\operatorname{Orbits}\left(G, X\right), K\right)\right)$$

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixedBasisEquivOrbitFunctions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward linear map descends the basis coefficients of a fixed vector to the actual orbit quotient. Its inverse assigns each basis vector its orbit coefficient and reconstructs the vector through the basis coordinate equivalence. Equivariance proves that the reconstructed vector is fixed.

**Theorem 1.2 (Invariant dimension equals the number of orbits).**

$$\forall K,G,X,V, \operatorname{Field}\left(K\right) \land \operatorname{Group}\left(G\right) \land \operatorname{MulAction}\left(G, X\right) \land \operatorname{Fintype}\left(X\right) \land \operatorname{AddCommGroup}\left(V\right) \land \operatorname{Module}\left(K, V\right) \Rightarrow \forall rho\in \operatorname{MonoidHom}\left(G, \operatorname{LinearAut}\left(K, V\right)\right), \forall b\in \operatorname{Basis}\left(X, K, V\right), (\forall g\in G, \forall x\in X, \operatorname{rho}\left(g, \operatorname{b}\left(x\right)\right)=\operatorname{b}\left(\operatorname{smul}\left(g, x\right)\right)) \Rightarrow \operatorname{finrank}\left(K, \operatorname{Fixed}\left(rho\right)\right)=\operatorname{card}\left(\operatorname{Orbits}\left(G, X\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixed_finrank_eq_orbit_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The linear equivalence identifies the fixed submodule with the finite function space on the orbit quotient, so its dimension is exactly the number of orbits. This extends the independent regular-orbit calculation to actions with stabilizers, without dividing by a group or stabilizer order.

This is a general algebraic bridge for pure permutation bases. A lattice lift carrying nontrivial scalar phases requires an additional stabilizer-character analysis; no assertion about the dimension of an entire lattice C2 quotient follows from this result alone.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixedBasisEquivOrbitFunctions`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FinitePermutationInvariants.fixed_finrank_eq_orbit_card`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FiniteGroupOrbitFixedLine](FiniteGroupOrbitFixedLine.md)
