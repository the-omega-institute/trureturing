# Fixed-label rational clearing and partial fractions

## Abstract

The exact i<j denominator admits a finite oriented normal form at every integer collision weight.

Fix z among N labels. Curry the z coordinate into a single rational-function variable over the fraction field of Laurent polynomials in all remaining labels. A numerator may have negative remaining exponents; only its z exponents must be nonnegative. The denominator is exactly Q=product over i<j of (z_i-z_j)^k.

**Theorem 1.1 (Preserve every original orientation scalar).**

Lean statement: `D5/S3/VertexAlgebra/LabelledRationalClearing.curry_clearingPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LabelledRationalClearing.curry_clearingPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Each labelled pair becomes a monic z-pole or a spectator scalar. When the original i<j factor has z as its second label, pairScalar contributes -1. ClearingScalar retains the product of all these factors; it is nonzero. No sign is discarded when monic poles are chosen.

**Theorem 1.2 (Finite partial fractions for all integer weights).**

Lean statement: `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_Q_partial_fractions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_Q_partial_fractions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

The factor (z-x)^r is separated using r.toNat and (-r).toNat. WeightedOrders adjusts the actual diagonal pole while every other labelled pole retains its order. Mathlib partial fractions supply a polynomial part and finitely many proper remainders from pairwise coprime monic factors.

**Theorem 1.3 (Constant numerators over the remaining rational field).**

Lean statement: `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Every nonconstant pole is linear, so each proper remainder is constant in z. The resulting finite q and c share the same oriented rational expression for both full orders. Currying and uncurrying are inverse fraction-field maps.

The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association is background, not a claim that these new rational proofs are supplied by that paper.

Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide residue-product locality and reconstruction background. Their reconstruction requires additional creative generators and a common translation operator. Carpi and Codogni, arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, CFT/anomaly/fusion, string theory or AdS/CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LabelledRationalClearing.curry_clearingPolynomial`
- Truth anchor: `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_Q_partial_fractions`
- Truth anchor: `D5/S3/VertexAlgebra/LabelledRationalClearing.weighted_actual_normal_form`
- Dependency: [D5/S3/VertexAlgebra/CollisionRationalExpansions](CollisionRationalExpansions.md)
