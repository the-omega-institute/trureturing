# Nilpotence

## Abstract

Nilpotence

This is the finite source-coordinate dependency of full corrected-field inversion. Arbitrary symmetric even integral lattices, rank zero, zero charge, empty supports and indefinite norms remain in scope. No positive energy, ground pairing or Jacobi premise is used.

**Theorem 1.1 (sectorL1_monomial_bound).**

Lean statement: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_monomial_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_monomial_bound` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The sharp R+1 bound uses exactly Finsupp.weight(sourceWeight D), proved by a sharp Leibniz-product induction.

**Theorem 1.2 (sectorL1_degree_bound).**

Lean statement: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_degree_bound`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_degree_bound` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The existing weighted total degree bounds the entire finite monomial support, including constants and zero. The proof directly reuses Mathlib's Module.End.pow_map_zero_of_le to extend the monomial annihilation bound.

**Theorem 1.3 (sugawara_pow_single).**

Lean statement: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_pow_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_pow_single` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The equality to existing Sugawara powers is consumed by the original-Carrier sharp bound and finite-flow expansion.

**Theorem 1.4 (sugawara_one_locally_nilpotent).**

Lean statement: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_one_locally_nilpotent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_one_locally_nilpotent` (`✓ std3`). ∎

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Finite charge support gives actual Sugawara local nilpotence without any assumption on signed charge norm. Mathlib's Module.End.pow_map_zero_of_le directly extends each finite-support annihilation bound to the common exponent.

The imported Sugawara architecture retains Kalle Kytola attribution. No literature novelty is claimed. Full all-source corrected-field adjointness, the K_L/K_R coefficient law and the complete Monster, VOA, CFT, fusion, string-theory and AdS/CFT goal remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_degree_bound`
- Truth anchor: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sectorL1_monomial_bound`
- Truth anchor: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_one_locally_nilpotent`
- Truth anchor: `D5/S3/VertexAlgebra/SourceMobius/Nilpotence.sugawara_pow_single`
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/PositiveMode](PositiveMode.md)
