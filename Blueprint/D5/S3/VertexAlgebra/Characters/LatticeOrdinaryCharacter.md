# Actual Ordinary Lattice Character

## Abstract

The full ordinary character of the actual positive even lattice Sugawara grading.

**Definition 1.1 (Literal full-grade dimension).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The coefficient at natural energy N is Module.finrank over the complex numbers of the literal eigenspace of sugawaraMode D H 0 with eigenvalue N. No finite surrogate or inserted trace defines it.

**Definition 1.2 (Vacuum-normalized ordinary character).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCharacter`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The character is exp(-2 pi i tau rank/24) times the natural-energy series of the literal full-grade dimensions. Its convergence and theta/eta value are conclusions below.

**Definition 1.3 (Natural total energy).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.totalDegree`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.totalDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The degree is Int.toNat of the actual label energy, with chargeEnergy plus oscillatorEnergy. Positive definiteness proves that this loses no energy information.

**Definition 1.4 (Complete energy-label fiber).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.NaturalEnergyFiber`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.NaturalEnergyFiber` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Every charge and oscillator occupation of the specified total energy is included; no charge cutoff occurs in this definition.

**Theorem 1.5 (Finite complete energy fibers).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.naturalEnergyFiber_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.naturalEnergyFiber_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every LatticeData D with positive definite real Gram matrix and every natural energy N, the complete natural-energy fiber is finite. The proof identifies it with the canonical integral-energy fiber.

**Theorem 1.6 (Finite literal Sugawara eigenspaces).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryGrade_finiteDimensional`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryGrade_finiteDimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For H with both H*gramComplex D = 1 and gramComplex D*H = 1, positivity identifies the full Sugawara eigenspace with its canonical finite charge cutoff. The existing cutoff basis proves finite dimensionality.

**Theorem 1.7 (Actual dimension counts all energy labels).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient_eq_card`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient_eq_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For the same inverse Gram equations and positivity, actualOrdinaryCoefficient D H N equals Nat.card of EnergyFiber D N. An explicit equivalence places every label into the charge ellipsoid, and the cutoff coefficient basis computes the literal full eigenspace dimension.

**Theorem 1.8 (Absolutely convergent all-label factorization).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.ordinary_label_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.ordinary_label_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every positive definite D and every complex tau with positive imaginary part, the full label q-series is absolutely summable and equals latticeTheta D tau times the unsigned oscillator occupation sum. Evenness identifies the charge exponent with the exact integral half-norm; Gaussian convergence and the established occupation majorant justify the product of sums.

**Theorem 1.9 (Absolutely convergent actual dimension series).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For both inverse Gram equations, positive definiteness and positive imaginary part of tau, the unnormalized series of actualOrdinaryCoefficient D H N times exp(2 pi i tau)^N is absolutely summable and has sum latticeTheta D tau times the unsigned occupation sum. Grouping both complex terms and their norms over finite complete energy fibers supplies the dimension coefficients.

**Theorem 1.10 (Actual ordinary character equals theta over eta to the rank).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_character`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_character` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For arbitrary LatticeData D, a complex inverse Gram matrix H satisfying both inverse equations, a positive definite real Gram matrix and tau in the upper half-plane, the vacuum-shifted series of literal Sugawara eigenspace finranks is absolutely summable, has sum latticeTheta D tau divided by eta(tau)^rank, and the defined actualOrdinaryCharacter has that value. The unsigned occupation Euler product and eta nonvanishing evaluate the oscillator factor.

All natural energies including zero and every rank including zero are in scope. The unsigned occupation helpers hold for every norm q less than one, including q zero. Rootlessness, unimodularity, rank parity and positive rank are not hypotheses. The reflecting trace character in LatticeThetaCharacter is a separate insertion-dependent quantity.

The ordinary lattice character formula is classical. Mathematical context is the lattice Fock construction of Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster, and the lattice construction in Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1, section 4.1. The existing FLM Library note verifies the bibliographic identity; the book full text was not inspected. Bakalov-Kac section 4.1 is the construction context. This proof reuses the canonical actual Sugawara grading, Gaussian convergence, AnalyticIntegerOccupation majorant, AnalyticOddOccupation Euler expansion and Mathlib Dedekind eta product with their original attribution and licenses. No literature novelty is claimed.

This establishes the ordinary analytic character of the existing lattice algebra and grading. It does not establish a Monster action, orbifold, modular-object or cusp-holomorphy theorem, sewing, string theory or AdS/CFT.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.NaturalEnergyFiber`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCharacter`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryCoefficient_eq_card`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actualOrdinaryGrade_finiteDimensional`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_character`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.actual_ordinary_series`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.naturalEnergyFiber_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.ordinary_label_series`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter.totalDegree`
- Dependency: [D5/S3/Arith/Lattices/LatticeThetaTransformation](../../Arith/Lattices/LatticeThetaTransformation.md)
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeThetaCharacter](LatticeThetaCharacter.md)
