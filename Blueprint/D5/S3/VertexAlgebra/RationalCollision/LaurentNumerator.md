# Unrestricted Laurent rational collision

## Abstract

Complete adjacent rational collision for unrestricted finite Laurent numerators and independent pair orders.

Over any field K, retain arbitrary finite pre/post blocks, an eliminated label z, an equivalence tau ordering every remaining label, and the adjacent label x with tau(pre)=x. The numerator is an arbitrary finitely supported labelled Laurent polynomial: every exponent is an integer, including that of z. Each labelled pair has its own natural denominator order. The diagonal residue weight r ranges over all integers.

**Theorem 1.1 (Collision of the actual divided rational in both complete orders).**

Lean statement: `D5/S3/VertexAlgebra/RationalCollision/LaurentNumerator.weighted_laurent_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/RationalCollision/LaurentNumerator.weighted_laurent_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Atsushi Matsuo; Kiyokazu Nagatomo (1997). *On axioms for a vertex algebra and the locality of quantum fields*. URL: <https://arxiv.org/abs/hep-th/9706118v1>.

*Commentary.*

A finite support lower bound clears negative z powers. Polynomial partial fractions are derived with the origin pole and every actual labelled pair pole, preserving the independent denominator orders and orientation scalars. The polynomial part and all pair terms use the existing additive collision calculus. The origin pole has equal residues in both complete adjacent orders; its residue in the local coordinate at the nonzero retained variable vanishes. No expansion compatibility or normal form is assumed.

The u=-1 coefficient of the complete fused local expansion equals the first full z=-1 fibre minus the second full residue. This is equality of entire remaining Hahn series, so every spectator exponent is retained. P/Q is formed before any spectator coefficient is selected; no origin term or finite block is discarded.

For the prospective actual nested-Q readout consumer, this removes the former nonnegative-z-numerator premise: a finite Laurent numerator produced by clearing the actual local denominators can be supplied directly, with its actual pair orders and signed diagonal weight. That external consumer still needs its own locality padding, coordinate maps, coefficient extraction and Taylor identifications. Its merge and the actual VOA realization are separate obligations.

Source proof: lexa-ms <50111876+AlyciaBHZ@users.noreply.github.com>, RationalCollision.LaurentNumerator in D5/S3/VertexAlgebra/RationalCollision.lean at immutable checkpoint 6c8682a64921b8f8d2f059c80e395b2af30c9a13; original proof checkpoint cda001f75ea0ca217d1230c9abbefd62265d44aa. The complete telescope and proof are preserved. This extraction claims no independent discovery. The locality LibraryNote is background.

The full-telescope Reg mirror contains a dependent/source registration attempt that preserves all original parameter and input fibers. Source-coordinate selection remains unfinished under https://github.com/the-omega-institute/trureturing/issues/20163. No declared_validated registration is claimed.

Polynomial partial fractions: Kevin Buzzard, Sidharth Hariharan and Aaron Liu; HahnSeries: Aaron Anderson; LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández and Filippo A. E. Nuccio, Apache 2.0. The imported rational collision owner gives the remaining upstream attribution. This generic rational theorem supplies no complete nested-Q/Taylor equality, Monster carrier identification, VOA reconstruction, CFT, anomaly, fusion, string theory or AdS/CFT realization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/RationalCollision/LaurentNumerator.weighted_laurent_collision`
- Dependency: [D5/S3/VertexAlgebra/RationalCollision](../RationalCollision.md)
