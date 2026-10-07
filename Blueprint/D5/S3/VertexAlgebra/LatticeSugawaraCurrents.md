# Actual Lattice Currents and Sugawara Coefficients

## Abstract

The genuine lattice currents obey Heisenberg and compute the finite coefficients of the quadratic field.

Let D be an even integral symmetric lattice of any finite rank, including zero. Its carrier is the finite-support sum over all integral charges of the complex oscillator polynomial algebra. The quadratic field is one half the H-weighted double sum of the actual normalMinusOne current products, with L(m) its normalized coefficient at m+1. Positive currents vanish beyond the largest frequency appearing in the actual input. Normal summands therefore have statewise finite support in [min(0,m-R),R]; this is not a uniform endomorphism cutoff.

**Theorem 1.1 (neutralField ncoeff).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralField_ncoeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralField_ncoeff` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every ordinary D, index i and integer k, the normalized coefficient (neutralField(D,i))[[k]] equals the actual neutralMode(D,i,k), on the whole all-charge carrier. No positive-form or inverse-Gram hypothesis is required.

**Theorem 1.2 (Actual Heisenberg law in every charge sector).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralMode_heisenberg`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralMode_heisenberg` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For all integers m,n and all lattice indices i,j, [h_i(m),h_j(n)]=m G(i,j) delta(m+n,0) id. Multiplication and Gram-weighted partial differentiation prove both mixed sign branches; zero currents are the actual charge scalars.

**Theorem 1.3 (The normal-product coefficient equals the statewise finite sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.sugawaraMode_interval_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.sugawaraMode_interval_sum` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

At coefficient m+1 the defining subtype equation has terms h_i(-t-1)h_j(m+t+1) and h_j(m-t)h_i(t). Reindexing the two natural sums gives respectively k<0 and k>=0, with N(i,j;k,l)=h_i(k)h_j(l) in the first half and h_j(l)h_i(k) in the second. Thus L(m)v is one half the H-weighted double sum of N(i,j;k,m-k)v over the stated finite interval. This is finite support on v, not on endomorphisms.

The weighted partial derivatives directly use the frozen private partials_commute of ConditionalPolynomialRigidity. The current contraction uses both inverse-Gram equations H Gc=Gc H=1. Bakalov-Kac, arXiv math/0402315v1, section 4.1, equations (4.12)-(4.16), supplies the classical lattice construction; the finite normal-ordering architecture is adapted from Kytola at revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralField_ncoeff`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.neutralMode_heisenberg`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeSugawaraCurrents.sugawaraMode_interval_sum`
- Dependency: [D5/S3/Quantum/Algebra/ConditionalPolynomialRigidity](../Quantum/Algebra/ConditionalPolynomialRigidity.md)
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](FieldNormalProduct.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeFiniteNegativeGeneration](LatticeFiniteNegativeGeneration.md)
