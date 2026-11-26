# Order-Three Twisted Lattice Charges

## Abstract

The concrete order-three lattice multiplier and the exact divisibility test for its moving-charge commutator.

Write ⟨a,b⟩ for the integral pairing on the native even charge lattice and use ζ = exp(2πi/3). The Lean formulas for B and c allow any additive equivalence g. The identification with Bakalov–Kac uses an order-three lattice isometry. The moving-charge laws assume g preserves the pairing and g³ = 1, with N = 1 + g + g².

**Definition 1.1 (Product factor).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.B`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.B` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For an order-three lattice isometry g, B(a,b) is the product factor of Bakalov–Kac, arXiv:math/0402315v3, equation (4.37). The factors are 3 to the power −⟨a,b⟩, (1 − ζ) to the power ⟨g a,b⟩, and (1 − ζ²) to the power ⟨g² a,b⟩. Each factor is a complex unit.

**Definition 1.2 (Charge multiplier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.c`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.c` (`✓ std3`).

*Citation.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The Lean formula c(a,b) = ε(a,b)/B(a,b) uses the native lattice sign ε as a unit. For an order-three lattice isometry g, this is the coefficient of U_(a+b) in U_a U_b in equation (4.42) of arXiv:math/0402315v3.

**Theorem 1.3 (The moving-charge commutator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For the order-three twist, equation (4.43) of arXiv:math/0402315v3 uses the order U_d U_b U_d⁻¹ U_b⁻¹. For d = a − g a, Lean proves that c(d,b)/c(b,d) is ζ to the power −⟨N a,b⟩. The swapped product factors use 1 − ζ² = (1 − ζ)(−ζ⁻¹). The lattice sign then has an even exponent, and the remaining exponent differs from −⟨N a,b⟩ by a multiple of three. With the compatible normalized lift of (4.18)–(4.19), this phase cancels the conjugation phase from the fixed part N a / 3 in the quotient relation (4.46).

**Theorem 1.4 (When the commutator is trivial).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_eq_one_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_eq_one_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The commutator equals one exactly when three divides ⟨N a,b⟩. Equivalently it is nontrivial precisely when that integer has nonzero residue modulo three. The test uses that ζ has order exactly three.

**Theorem 1.5 (Dependence on the difference charge and orbit norm).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_congr`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The commutator is unchanged when a is replaced by a′ with a − a′ fixed by g and b is replaced by b′ with N b = N b′. The first condition preserves the difference charge. For the second, the isometry and g³ = 1 give ⟨N a,b⟩ = ⟨a,N b⟩.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.B`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.c`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_congr`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle.commutator_difference_eq_one_iff`
- Dependency: [D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift](../CyclicIsometryLift.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](../../LatticeActualProductKernel.md)
