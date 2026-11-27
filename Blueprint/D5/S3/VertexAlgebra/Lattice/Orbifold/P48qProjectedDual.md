# P48q Gram Dual and Projected Charges

## Abstract

The P48q lattice equals its Gram dual, and the dual of its integral fixed lattice is the image of the order-three average on integral charges.

Use the Nebe–Sloane P48q catalogue basis with coordinates indexed by Fin 48. Let G be the integral Gram matrix and B its complex bilinear extension. Write ι for coordinatewise inclusion of the integer rows into the complex rows. Let A be the fourth power of the first catalogue generator, acting on rows by right multiplication. Write T for its complex linear extension and N = I + A + A² for the integral cyclic norm.

**Theorem 1.1 (The ambient Gram dual).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.gram_dual_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.gram_dual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Commentary.*

For every complex row μ, the pairing B(ι(x), μ) is an integer in ℂ for every integer row x if and only if μ = ι(a) for some integer row a.

Testing the coordinate unit rows gives an integral column Gμᵀ. Applying the certified integral inverse recovers integral coordinates for μ. In the reverse direction, the Gram matrix has integer entries.

**Theorem 1.2 (The fixed dual is the image of the average).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.fixed_dual_iff_projected_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.fixed_dual_iff_projected_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gabriele Nebe (2014). *A fourth extremal even unimodular lattice of dimension 48*. DOI: [10.1016/j.disc.2014.05.011](https://doi.org/10.1016/j.disc.2014.05.011). URL: <https://arxiv.org/abs/1312.3780v2>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every complex row μ, the conjunction of Tμ = μ and integrality of B(ι(x), μ) for every integer row x with xA = x holds if and only if μ = ι(aN)/3 for some integer row a.

The isometry gives B(ι(x), 3μ) = B(ι(xN), μ) when μ is fixed. Since xN is fixed, the ambient dual theorem puts 3μ in the integral lattice. The integral norm-image certificate supplies a with ι(aN) = 3μ. Conversely, the average of a is fixed and pairs with any fixed integral x exactly as a does.

This is the P48q coordinate proof of the lattice equality (Q ∩ h₀)* = π₀(Q*) used after equation (4.56) of Bakalov–Kac, arXiv:math/0402315v1, with the projection-duality identity in Lemma 4.6. Here the ambient dual equals Q and π₀ is the order-three average.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.fixed_dual_iff_projected_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/P48qProjectedDual.gram_dual_iff`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramCertificate](P48qGramCertificate.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/Orbifold/P48qNormImageCertificate](P48qNormImageCertificate.md)
