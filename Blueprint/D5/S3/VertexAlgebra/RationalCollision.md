# Full fixed-denominator rational collision

## Abstract

The complete rational collision holds for every integer weight and every remaining labelled exponent.

Over any field K, take arbitrary finite pre/post blocks, z, tau, x with tau(pre)=x, a finite labelled Laurent numerator P whose z exponents are nonnegative, and the exact fixed-label Q of order k. Divide P by Q in the common rational field. Expand in the two complete orders before selecting the supported z=-1 fibres.

**Theorem 1.1 (Assemble the collision without a decomposition premise).**

Lean statement: `D5/S3/VertexAlgebra/RationalCollision.full_collision_series`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RationalCollision.full_collision_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The oriented finite partial-fraction normal form is derived from the actual weighted P/Q. Polynomial residue zero, the all-integer diagonal kernel and spectator cancellation prove each term. Additive residue maps assemble equality of entire supported Hahn series on every remaining label.

**Theorem 1.2 (All integer weights and all remaining labelled coefficients).**

Lean statement: `D5/S3/VertexAlgebra/RationalCollision.required_proved`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RationalCollision.required_proved` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The theorem discharges the full CollisionStatement with no assumed collision, support certificate or compatibility law. It quantifies r in Int and every function from Remaining z to Int. Negative remaining exponents and arbitrary spectators are retained.

**Theorem 1.3 (Expand the fused local rational before taking residue).**

Lean statement: `D5/S3/VertexAlgebra/RationalCollision.complete_expansion_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RationalCollision.complete_expansion_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The fused-residue square identifies the u=-1 coefficient of the complete remaining expansion with the local rational residue. It equals the difference of the two complete supported z=-1 fibres of (z-x)^r P/Q. This is a rational collision theorem; fusedLocalSeries is not an identified state iterate.

The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association is background, not a claim that these new rational proofs are supplied by that paper.

Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide residue-product locality and reconstruction background. Their reconstruction requires additional creative generators and a common translation operator. Carpi and Codogni, arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, CFT/anomaly/fusion, string theory or AdS/CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RationalCollision.complete_expansion_collision`
- Truth anchor: `D5/S3/VertexAlgebra/RationalCollision.full_collision_series`
- Truth anchor: `D5/S3/VertexAlgebra/RationalCollision.required_proved`
- Dependency: [D5/S3/VertexAlgebra/LabelledRationalClearing](LabelledRationalClearing.md)
- Dependency: [D5/S3/VertexAlgebra/OrderedCollisionCoordinates](OrderedCollisionCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/OrderedCollisionResidues](OrderedCollisionResidues.md)
