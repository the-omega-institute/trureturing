# All-integer Laurent collision kernels

## Abstract

The two iterated Laurent expansions of a rational expression have a diagonal residue jump over any field.

**Theorem 1.1 (Coefficients of the complete actual word).**

Lean statement: `D5/S3/VertexAlgebra/CollisionLaurentKernels.ordered_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionLaurentKernels.ordered_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The exponent vector records coefficients in the recursively ordered Hahn group. The coefficient at e is the successive mode action with mode index -e_i-1. Scalar evaluation is a linear map applied after that action, with the same operator ordering.

Let K be any field. The labelled variables are z and x; the two iterated Laurent fields encode the orders z,x and x,z. Rational functions are divided in the common fraction field before either expansion. Integer powers, including inverse powers, are handled by the native Hahn and Laurent field maps.

**Theorem 1.2 (Diagonal poles at every integer power).**

Lean statement: `D5/S3/VertexAlgebra/CollisionLaurentKernels.diagonal_pole_jump`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionLaurentKernels.diagonal_pole_jump` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Generalized binomial coefficients give the coefficients of the two expansions of (z-x)^r for every integer r. The boundary binomial identity yields the difference of their z-residues. The original orientation is z-x; the reverse expansion retains its integer power of minus one.

**Theorem 1.3 (Finite numerators preserve the collision).**

Lean statement: `D5/S3/VertexAlgebra/CollisionLaurentKernels.finite_numerator_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionLaurentKernels.finite_numerator_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Induction on polynomial monomials transports the diagonal kernel through the numerator. The recurrence multiplies by z=x+u on the local side. The conclusion quantifies every integer weight and keeps the rational residue, rather than assuming a coefficient-compatibility law.

**Theorem 1.4 (Rational coefficients commute with local residue).**

Lean statement: `D5/S3/VertexAlgebra/CollisionLaurentKernels.rational_monomial_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionLaurentKernels.rational_monomial_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Injective polynomial maps lift to fraction fields. The translated rational and the fused coefficient-field expansion form a proved square; coefficientwise base change commutes with the u-residue. Separated poles supply the spectator cancellation kernel.

The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association is background, not a claim that these new rational proofs are supplied by that paper.

Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide residue-product locality and reconstruction background. Their reconstruction requires additional creative generators and a common translation operator. Carpi and Codogni, arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, CFT/anomaly/fusion, string theory or AdS/CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CollisionLaurentKernels.diagonal_pole_jump`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionLaurentKernels.finite_numerator_collision`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionLaurentKernels.ordered_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionLaurentKernels.rational_monomial_collision`
- Dependency: [D5/S3/VertexAlgebra/UniformGradedLocalCorrelator](UniformGradedLocalCorrelator.md)
