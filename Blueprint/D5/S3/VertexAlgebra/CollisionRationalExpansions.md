# Ordered rational expansions and residue fibres

## Abstract

A common labelled rational field embeds injectively into each complete supported order.

Labelled polynomials are finite Laurent polynomials in every label. Additive exponent equivalences transport them into the recursive lexicographic Hahn groups without dropping spectators. The injective polynomial maps lift to actual fraction-field maps. Coefficients are selected from these complete expansions, after division in the global rational field.

**Theorem 1.1 (Faithful polynomial and rational expansion).**

Lean statement: `D5/S3/VertexAlgebra/CollisionRationalExpansions.orderedPolynomialFor_injective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionRationalExpansions.orderedPolynomialFor_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Any finite permutation sigma gives an injective ordered polynomial map. Its fraction-field extension evaluates the same labelled rational expression in that order. Actual words are supported by their native field composition, rather than by a new support hypothesis.

**Theorem 1.2 (Supported coefficient fibres and scalar multiplication).**

Lean statement: `D5/S3/VertexAlgebra/CollisionRationalExpansions.pullFiber_mul`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionRationalExpansions.pullFiber_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

An order-preserving insertion identifies the fixed z-exponent fibre with a supported Hahn series on the remaining coordinates. The support is derived from the original series support. Finite antidiagonal multiplication proves compatibility with remaining-variable scalars.

**Theorem 1.3 (Nonadjacent spectator poles cancel in complete orders).**

Lean statement: `D5/S3/VertexAlgebra/CollisionRationalExpansions.nonadjacent_spectator_factor_cancel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CollisionRationalExpansions.nonadjacent_spectator_factor_cancel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

Explicit inserted coordinates relate the two adjacent full orders. A spectator coordinate outside the adjacent position gives equal residue contributions in the two orders, including powers and arbitrary supported scalar coefficients. No spectator coefficient is extracted before the full rational expansion.

The algebraic proofs reuse mathlib Hahn/Laurent support, finite antidiagonal multiplication, fraction-field lifts and polynomial partial fractions. LaurentSeries authors are Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio; HahnSeries author is Aaron Anderson; partial fractions authors are Kevin Buzzard, Sidharth Hariharan and Aaron Liu. These sources carry Apache 2.0 licenses. Actual HVertexOperator and VertexOperator composition are by Scott Carnahan, Apache 2.0. The imported FieldNormalProduct supplier attributes its support/Hasse adaptation to ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. The locality LibraryNote association is background, not a claim that these new rational proofs are supplied by that paper.

Matsuo and Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1 provide residue-product locality and reconstruction background. Their reconstruction requires additional creative generators and a common translation operator. Carpi and Codogni, arXiv:2605.26972v1, Conjecture 14.4 concerns all weights; Proposition 14.3 treats k<24. The corrected coefficient is D(h,j)=j!(2h)_j; the faulty printed Equation 46 is unused here. No proof of that conjecture, actual Moonshine/PCT, a fused-state energy law, CFT/anomaly/fusion, string theory or AdS/CFT is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CollisionRationalExpansions.nonadjacent_spectator_factor_cancel`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionRationalExpansions.orderedPolynomialFor_injective`
- Truth anchor: `D5/S3/VertexAlgebra/CollisionRationalExpansions.pullFiber_mul`
- Dependency: [D5/S3/VertexAlgebra/CollisionLaurentKernels](CollisionLaurentKernels.md)
