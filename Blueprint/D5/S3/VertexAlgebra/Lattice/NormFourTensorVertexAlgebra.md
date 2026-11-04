# The Actual Range and Tensor Vertex Algebras

## Abstract

The actual minus-one tensor map realizes a vertex algebra on its range and on the literal tensor product.

Let D be arbitrary production lattice data, a a charge with bilinear(D,a,a)=4, and s a complex scalar with s squared equal to one. Put S=NormFourVacuumIrreducible.vacuumDescendants(D,a,s) and C=NormFourCommutant.space(D,a,s), the literal production subspaces. Let T be the algebraic tensor product S tensor C over the complex numbers. Use the existing complex-linear F=NormFourTensorEmbedding.tensorMap(D,a,s), with F(u tensor b)=Y(b)_(-1)u, and let R be its actual linear-map range.

**Definition 1.1 (The actual range vertex algebra).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.rangeVertexAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.rangeVertexAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,ha,s,hs as above, rangeVertexAlgebra is a StateFieldVertexAlgebra on R. Its vacuum, every integer field coefficient and translation are the restrictions of the actual ambient ones. Its fields are genuine Hahn-module series with statewise partially well-ordered support. The structure proves the vacuum field, creation, creativity, translation of the vacuum, covariance, locality under an iterated delta, and the full Borcherds identity for every integer p,q,r, including finite support of its left, first and second families.

**Definition 1.2 (The vertex algebra on the literal tensor product).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.tensorVertexAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.tensorVertexAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same full parameter telescope, tensorVertexAlgebra is a StateFieldVertexAlgebra on T. LinearEquiv.ofInjective applied to the existing F and its proved injectivity identifies T with R. Conjugating the range coefficients and translation and pulling back the range vacuum constructs the tensor data. The operators have statewise Hahn truncation; locality and the full p,q,r Borcherds identity, with all three finite-support clauses, hold on T.

**Theorem 1.3 (All states, every integer coefficient and actual translation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.actual_tensor_vertex_algebra_embedding`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.actual_tensor_vertex_algebra_embedding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,ha,s,hs as above, write V_R and V_T for these two algebras. F is injective. The actual vacuum belongs to R. For every ambient u,v belonging to R and every integer n, Y(u)_n v belongs to R; actual translation also maps every v in R into R. The inclusion of V_R takes its vacuum to the ambient vacuum, every coefficient on every pair of range states to the corresponding ambient coefficient, and its translation on every range state to actual translation.

V_T.vacuum is exactly the pure tensor of the vacuum of NormFourVacuumVertexAlgebra.vertexAlgebra(D,a,ha,s,hs) and the vacuum of NormFourCommutant.restrictedVertexAlgebra(D,a,s). F takes it to the actual ambient vacuum. For every u,v in the entire T and every integer n, F((V_T.stateField(u))_n v)=Y(F(u))_n F(v). For every v in T, F(V_T.translation(v)) equals actual translation of F(v).

For a left pure tensor u tensor b and an arbitrary right tensor z, apply the actual iterate to b,u,F(z) with r=-1 and arbitrary integer n. Its complete first family has terms (-1)^i choose(-1,i) Y(b)_(-1-i)Y(u)_(n+i)F(z). S-side intertwining first places the inner coefficient in R, and C-side intertwining places the outer one there. The complete second family has terms (-1)^i choose(-1,i) Y(u)_(-1+n-i)Y(b)_i F(z). Here C-side intertwining followed by S-side intertwining gives membership. Both actual finite-support hypotheses turn the families into finite submodule sums; the second sum and its scalar (-1)^(-1) are retained. Tensor induction in the left argument extends closure to every left tensor while the right tensor remains arbitrary. Taking range preimages gives closure for every pair in R.

The existing tensor vacuum identity gives actual vacuum membership. LatticeActualVertexAlgebra.translation_as_mode expresses actual translation as the -2 coefficient on that vacuum, so coefficient closure gives translation closure. Restricting the ambient coefficients constructs genuine Hahn operators. An injective coefficient map preserves the vacuum, translation, every iterated locality delta and finite sums; injectivity also reflects support, giving all three Borcherds supports. This proves the laws both for range inclusion and for the linear equivalence from T. Injectivity of F and the existing pure tensor vacuum image identify the transported vacuum with the natural tensor vacuum.

F and its injectivity, S-mode intertwining and vacuum identity are from NormFourTensorEmbedding; C-mode intertwining is from NormFourTensorCommutantModes. Coefficient inheritance follows the literal subtype constructions in NormFourVacuumVertexAlgebra and NormFourCommutant, using LatticeActualVertexAlgebra.StateFieldVertexAlgebra. The iterate is LatticeAllStateReconstruction.stateField_iterate in LatticeAllStateLocality. The lattice fields retain Bakalov-Kac, math/0402315, section 4.1 attribution; the norm-four construction retains Dong-Mason-Zhu, Theorem 6.3 and Shimakura, arXiv:1202.6107, (1.3) attribution. The residue and normal-product constructions retain their Scott Carnahan and Matsuo-Nagatomo attribution and imported Apache 2.0 notices. This is an ungraded embedded vertex algebra. No positivity, rootlessness, extra finiteness, abstract Ising identification, ambient surjectivity or ambient factorization is assumed. Conformal and grading extensions, rationality, fusion, Monster moonshine, analytic CFT, string theory and AdS/CFT remain further mathematical questions; no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.actual_tensor_vertex_algebra_embedding`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.rangeVertexAlgebra`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra.tensorVertexAlgebra`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourTensorCommutantModes](NormFourTensorCommutantModes.md)
