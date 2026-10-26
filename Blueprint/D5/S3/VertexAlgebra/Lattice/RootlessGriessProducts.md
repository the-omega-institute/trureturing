# Actual Rootless Lattice Quadratic and Charge Products

## Abstract

Actual quadratic and norm-four charge-orbit products in the production lattice vertex algebra.

**Definition 1.1 (Neutral quadratic state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Q`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For any even LatticeData D and colours i,j, Q is the zero-charge polynomial X(i,0) X(j,0) in the actual finite-charge carrier. Repeated colours are allowed.

**Definition 1.2 (Charged ground state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.ground`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.ground` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The state at an integral charge a is the literal finitely supported vector with polynomial one in charge sector a.

**Definition 1.3 (Plus charge orbit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.E`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

E(a) is ground(a) plus ground(-a), with no representative choice. Equal and opposite charges describe the same orbit state.

**Definition 1.4 (Gram-charge contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Gi`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Gi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Gi(i,a) is the complex cast of the sum over colours j of G(i,j) times the integral coordinate a(j).

**Definition 1.5 (Actual charge-oscillator square).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Qcharge`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Qcharge` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Qcharge(a) is the zero-charge state whose polynomial is the square of the existing mode-one chargePolynomial(a).

**Theorem 1.6 (Four quadratic contractions at mode one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For all colours i,j,k,l of every even LatticeData D, the actual normalized product mu(Q(i,j),1,Q(k,l)) is G(i,k) Q(j,l) plus G(i,l) Q(j,k) plus G(j,k) Q(i,l) plus G(j,l) Q(i,k), with matrix entries cast to complex scalars. This includes coincident colours and requires no inverse Gram matrix or positive-rank hypothesis.

**Theorem 1.7 (Actual quadratic vacuum pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_three`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual mode-three coefficient mu(Q(i,j),3,Q(k,l)) equals (G(i,k) G(j,l) plus G(i,l) G(j,k)) times the actual vacuum, for arbitrary even LatticeData and all colours.

**Theorem 1.8 (Quadratic action on a plus orbit).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_orbit_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_orbit_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every integral charge a and colours i,j, mu(Q(i,j),1,E(a)) equals Gi(i,a) Gi(j,a) times E(a). No charge-norm or positivity premise is used.

**Theorem 1.9 (Reversed mixed contraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_quadratic_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_quadratic_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every integral charge a and colours i,j, mu(E(a),1,Q(i,j)) equals Gi(i,a) Gi(j,a) times E(a). Actual all-state skew symmetry gives this direction after every positive-translation tail coefficient vanishes.

**Theorem 1.10 (Both mixed vacuum pairings vanish).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.mixed_three`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.mixed_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every integral charge a and colours i,j, both actual coefficients mu(Q(i,j),3,E(a)) and mu(E(a),3,Q(i,j)) vanish. The theorem states their conjunction on the production carrier.

**Theorem 1.11 (Complete rootless charge product at mode one).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_one`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Let D be an even LatticeData whose real-cast Gram matrix is positive definite and whose integral charges never have norm two. For arbitrary charges a,b, each of norm four, mu(E(a),1,E(b)) is Qcharge(a) if b equals a or -a. Otherwise it is epsilon(a,b) times E(a+b) when the Gram pairing is -2, epsilon(a,-b) times E(a-b) when the pairing is 2, and zero in the remaining cases. Positivity and rootlessness bound the pairing using both a-b and a-(-b); no Cauchy estimate is assumed. In the coincident orbit the actual second creation coefficients cancel their derivative terms and leave the charge-oscillator square. The phases are the literal lower-cocycle epsilon.

**Theorem 1.12 (Complete rootless charge vacuum pairing).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_three`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Under the same positive-definiteness, rootlessness and two norm-four premises, the actual coefficient mu(E(a),3,E(b)) is twice the vacuum if b equals a or -a, and zero otherwise. The proof extracts actual ground-series coefficients rather than assuming a bilinear pairing.

All products use the existing Carrier, Y, normalized integer-mode mu, translation, integral Gram pairing and lower cocycle. The derivations reuse quadratic_state_field, quadraticSummand_current_commutator, neutralMode_heisenberg, the actual ground series, the derivative-state theorem, all-state skew symmetry and chargeEnergy_gap. The Gram-coordinate and norm-difference formulas are those of LatticeFiniteNegativeGeneration.

Classical construction context is Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 section 4.1, and Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster. The actual normal-product and residue suppliers retain Carnahan, Matsuo-Nagatomo and Kytola attribution and their Apache-2.0 licenses. No literature novelty is claimed.

Rank zero and empty norm-four shells remain in scope. These are local product tables in the existing lattice vertex algebra; Monster, Ising, Peirce and simplicity results, fusion, anomalies, CFT, string theory and AdS/CFT remain outside these statements.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.E`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Gi`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Q`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.Qcharge`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.ground`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.mixed_three`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_orbit_three`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.orbit_quadratic_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_orbit_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_one`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.quadratic_quadratic_three`
- Dependency: [D5/S3/VertexAlgebra/Lattice/RootlessLowGrades](RootlessLowGrades.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](../LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../LatticeActualStateDerivative.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../LatticeInvolution.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorGround](../Sectors/LatticeSectorGround.md)
- Dependency: [D5/S3/VertexAlgebra/StateField/SkewSymmetry](../StateField/SkewSymmetry.md)
