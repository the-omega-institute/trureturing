# The actual full BRST Delta has a graded second-order product law

## Abstract

The actual full BRST Delta has a graded second-order product law

All quotient statements use the existing Cohomology D H h26 hHG hGH, the existing product (mode -1), the existing parity involution, and Delta from LatticeBRSTZeroEnergyReduction. The parameters are D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, h26 : D.rank = 26, hHG : H * gramComplex D = 1, and hGH : gramComplex D * H = 1. Neither the carrier, charge, cycles nor boundaries are replaced. No restriction on charge, positivity, oscillator number, ghost occupations, or energy is imposed.

Write mu_n(x,y) for originalMode D n x y, B_j for ghostB D j, P for the actual state parity, Q for totalCharge D H, and T for the actual translation. The actual odd state beta = matter vacuum tensor ket {0} has beta mode n equal to B_(n-1), using the native vacuum-mode and ghost creation suppliers. The native supported Borcherds identity at (1,n,0), with both reverse parity families retained, gives B_0(mu_n(x,y)) - mu_n(Px,B_0 y) = mu_n(B_0 x,y) + mu_(n+1)(B_(-1)x,y). Translation covariance and the signed iterate prove the needed residue mu_0(Tx,y) = 0.

**Definition 1.1 (The actual antighost descent current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.descentCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.descentCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D, descentCurrent D is the bilinear state map K(x,y) = mu_0(B_(-1)x,y). It is defined independently of Delta and product. B_(-1)x need not be a cycle. The native charge-mode law, {Q,B_(-1)} = T, antighost oddness, and the translation residue give Q K(x,y) = -K(Qx,y) - K(Px,Qy). Thus K acts on pairs of cycles; if x = Qz its primitive is -K(z,y), and if y = Qz its primitive is -K(Px,z).

**Definition 1.2 (Independent bilinear descent through the actual full quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.cohomologyCurrent`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.cohomologyCurrent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Under the full critical telescope, cohomologyCurrent is the bilinear map Kbar induced by these explicit cycle and boundary certificates through both arguments of the existing quotient. Its value at [x],[y] is [mu_0(B_(-1)x,y)] for arbitrary cycles x,y. No quotient mode-vanishing statement is applied to the generally nonclosed state B_(-1)x.

**Theorem 1.3 (Delta's product defect is the independently descended current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_product_defect`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_product_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a,b in Cohomology D H h26 hHG hGH, Delta(product(a,b)) - product(Delta(a),b) - product(parity(a),Delta(b)) = Kbar(a,b). Both classes may have mixed parity and mixed energy. The proof first replaces cycles by their actual P0 representatives without changing classes. For two zero-energy cycles, applying Q to the all-state antighost identity proves that their original -1 product also has totalL0 zero, so P0 fixes precisely that product. This uses the actual Ward identity and current cochain law, and makes no assertion that P0 is multiplicative on arbitrary states.

**Definition 1.4 (The scalar-sign form of the Delta defect).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.homogeneousDefect`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.homogeneousDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any natural p and quotient classes a,b, F_p(a,b) is Delta(product(a,b)) - product(Delta(a),b) - (-1)^p times product(a,Delta(b)). If parity(a) = (-1)^p times a, then F_p(a,b) = Kbar(a,b). The usual signed Lian-Zuckerman bracket on homogeneous first input is (-1)^p times F_p(a,b); no separate bracket or BV structure record is introduced.

**Theorem 1.5 (Graded Leibniz for Delta's actual full-quotient defect).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_second_order`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural p,q and classes a,b,c, assuming parity(a) = (-1)^p times a and parity(b) = (-1)^q times b, the exact conclusion is F_p(a,product(b,c)) = product(F_p(a,b),c) + (-1)^((p+1)*q) times product(b,F_p(a,c)). The class c is arbitrary. The native zero-mode derivation for B_(-1)u, whose parity is shifted from p to p+1, descends using homogeneous cycle lifts for a,b and an unrestricted cycle lift for c. Combined with the defect comparison, this is the second-order product law for the existing Delta.

The low-mode mechanism follows the historical OriginalTopologicalApplications proof (SHA256 85302c4b23c6e4e0f271ca7aa794ba69c65fbef4af813ca5e0204940696d95ad) while using only current native suppliers and the current quotient. Attribution remains with Bakalov-Kac, Scott Carnahan's vertexAlg residue calculus, Kalle Kytola's Sugawara suppliers, the ghost construction, and Mathlib. This is a constructive formal bridge within the actual lattice BRST complex; no literature novelty, Gerstenhaber Jacobi identity, full BV structure, complete string theory, spacetime reconstruction, or AdS/CFT correspondence is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_product_defect`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.Delta_second_order`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.cohomologyCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.descentCurrent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder.homogeneousDefect`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct](LatticeBRSTCohomologyProduct.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction](LatticeBRSTZeroEnergyReduction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostBorcherds](LatticeMatterGhostBorcherds.md)
