# Integer convolution and natural tensor translation

## Abstract

The actual literal tensor vertex algebra has finite integer field convolution and natural tensor translation.

Let D be arbitrary production lattice data, a a charge, ha an identity bilinear(D,a,a)=4, s a complex scalar and hs an identity s squared equals one. Put S=NormFourVacuumIrreducible.vacuumDescendants(D,a,s) and C=NormFourCommutant.space(D,a,s). Use the literal tensor product S tensor C over the complex numbers and the actual algebras V_S=NormFourVacuumVertexAlgebra.vertexAlgebra(D,a,ha,s,hs), V_C=NormFourCommutant.restrictedVertexAlgebra(D,a,s), and V_T=NormFourTensorVertexAlgebra.tensorVertexAlgebra(D,a,ha,s,hs). The map F is the original NormFourTensorEmbedding.tensorMap(D,a,s), with F(u tensor b)=Y(b)_(-1)u.

**Theorem 1.1 (Finite support and every integer field coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_field_convolution`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_field_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,ha,s,hs as above, all u,v in S, all b,c in C, and every integer n, define f(k)=((V_S.stateField(u))_k v) tensor ((V_C.stateField(b))_(n-1-k) c) for every integer k. Then f has finite support, and (V_T.stateField(u tensor b))_n(v tensor c) is exactly the finite-support sum of f(k) over all integers k. The assertion holds for arbitrary factor states, including zero states.

**Theorem 1.2 (The global natural translation operator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_translation_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_translation_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,a,ha,s,hs as above, V_T.translation equals the sum of the complex-linear maps TensorProduct.map(V_S.translation,id_C) and TensorProduct.map(id_S,V_C.translation) on the entire literal tensor space. In the same assertion, for every u in S and b in C, V_T.translation(u tensor b)=(V_S.translation(u)) tensor b + u tensor (V_C.translation(b)).

Apply the actual complete residue iterate to b,u,F(v tensor c), with r=-1 and arbitrary integer n. For every natural i, minus_one_binomial proves (-1)^i choose(-1,i)=1. The first complete family becomes F(((V_S.stateField(u))_(n+i)v) tensor ((V_C.stateField(b))_(-1-i)c)); the second becomes F(((V_S.stateField(u))_(n-1-i)v) tensor ((V_C.stateField(b))_i c)). The outer subtraction and (-1)^(-1) give a positive second sum. Both actual natural finite supports are reflected through the already proved injection of F. Equiv.subRight(n) followed by Equiv.intEquivNatSumNat has inverse branches k=n+i and k=n-1-i, so the two complete finite families reindex to the integer convolution. The accepted all-S and all-C mode intertwinings identify every summand. Full coefficient preservation for V_T and injectivity of F turn the private ambient image equality into the stated actual tensor field equality.

Actual stateField_covariance and state_derivative_modes at mode -1 give T(Y(b)_(-1)u)=Y(Tb)_(-1)u+Y(b)_(-1)Tu. Both factor translations are restrictions of this same ambient T. The actual pure-product formula for F therefore identifies this with F((V_S.translation(u)) tensor b + u tensor (V_C.translation(b))). The accepted full-state translation preservation and injectivity of F prove the pure-pair equality. Mathlib TensorProduct.ext extends it to the equality of linear maps on the whole tensor space.

The actual tensor algebra and its full embedding laws are from NormFourTensorVertexAlgebra. The factor mode intertwinings are from NormFourTensorEmbedding and NormFourTensorCommutantModes; the complete iterate is LatticeAllStateReconstruction.stateField_iterate in LatticeAllStateLocality. The lattice fields retain Bakalov-Kac, math/0402315, section 4.1 attribution; the norm-four construction retains Dong-Mason-Zhu, Theorem 6.3 and Shimakura, arXiv:1202.6107, (1.3) attribution. Imported residue and normal-product kernels retain Scott Carnahan and Matsuo-Nagatomo attribution and Apache 2.0 notices, including ScottCarnahan/vertexAlg commit 4453e34ec390e82a0c789c731ada8f9a6e86bdea, VertexAlg/VertexBasic/VertexOperator.lean. No literature novelty is claimed. The proof adds no support, nonzero-state, surjectivity, conformal, grading, rationality or fusion premise. Conformal extensions, Monster moonshine, CFT, string theory and AdS/CFT remain outside these two conclusions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_field_convolution`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourTensorConvolution.actual_tensor_translation_split`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourTensorVertexAlgebra](NormFourTensorVertexAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../LatticeActualStateDerivative.md)
