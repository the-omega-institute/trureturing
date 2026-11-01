# Corrected conformal state on the actual half-Fock module

## Abstract

The actual corrected conformal state is the native half-Fock tensor stress field.

**Theorem 1.1 (Actual neutral charged field is the identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_charged_zero_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_charged_zero_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The unchanged zero-charge calculation is public for the canonical GroundCompression consumer. Zero-charge translation is constant, the creation exponential is one, and the ground representation sends its identity to the identity. This is the actual chargedField on the entire tensor module.

**Theorem 1.2 (Identity field coefficient supplier).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_identity_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_identity_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The unchanged identity-field coefficient proof is public and consumed by canonical GroundCompression: for every integer exponent e and every tensor state v, its coefficient is v if e=0 and zero otherwise.

Let D be an integral symmetric even-diagonal lattice datum of arbitrary finite rank, hu:IsUnit D.G.det, and H any complex rank-by-rank matrix satisfying H*gramComplex(D)=1. There is no positive-rank, positivity, symmetry-of-H, homogeneity or eigenstate assumption. The source omega is the ordinary quadratic state single(0,(1/2) smul sum_i sum_j H(i,j) smul X(i,0)*X(j,0)). Its target is the full actual algebraic tensor space Oscillator(D) tensor_C ActualGround(D,hu). Rank zero is included.

The field on the left is correctedField from the original finite Corr and actual normal polynomial field, using the genuine Hahn shift S_s with coefficient e+2*s. At charge zero the charged field is the identity. The public singletonLinear operation inserts the actual half-integer current with negative modes acting on the left and nonnegative modes on the right. Polynomial multiplication by an oscillator agrees with this singleton insertion, with all occurrence multiplicities retained.

The quadratic finite correction is Corr(0,X(i,0)*X(j,0)) = single(0,X(i,0)*X(j,0)) + single(2,C(Gram(i,j)/8)). This also holds for i=j. Each normal-pair coefficient vanishes at odd e; at even e it is the pointwise finite signed mode sum at Virasoro mode m=(-e-4)/2. The established tensor-current truncation bounds this sum on every actual tensor vector.

Summing the quadratic fields with H(i,j)/2 gives tensorRawL at m=(-e-4)/2 and a correction supported exactly at e=-4. Its scalar is (sum_i sum_j H(i,j)*Gram(i,j))/16. The actual left-inverse equation and symmetry of the Gram matrix identify this contraction with rank(D). Thus the coefficient at -4 is tensorRawL(D,ActualGround(D,hu),H,0)v + (rank(D)/16) smul v for every actual tensor vector v. The equality is between whole native Hahn fields, not only vacuum coefficients or homogeneous components.

**Theorem 1.3 (Actual corrected omega equals tensor stress).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.correctedField_omega`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.correctedField_omega` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every D:LatticeData, hu:IsUnit D.G.det, arbitrary H and hHG:H*gramComplex(D)=1, correctedField D hu (LatticeActualConformalState.omega D H) equals tensorStressField D (ActualGround D hu) H. No field equality, module law or coefficient identity is a premise. With the actual integral inverse mapped to Complex, hHG follows from Matrix.nonsing_inv_mul and Matrix.map_mul. The ordinary identity LatticeActualConformalState.Y_omega concerns the ordinary state-field map; the present conclusion identifies the corrected half-Fock field.

The quadratic correction, normal-pair coefficient and inverse-trace argument reuse the conformal-identification proof source 27b7b753a978d7bd4555ccde3920ef412fd03d0b030341c7f0710f230c981fa6, through the candidate 3aa911340d71bfbbb80b42762ab4fecb2b523654c64810cafa00b1a4d4ddb408. The zero-charge proof bodies derive from source cd19be514c7c3bf81f4267e41e71524fcef62324e5c5f7183a41408d2eeecac0. The insertion formulas use the canonical FockNormalField public APIs. Inherited implementation copyright (c) 2025 Kalle Kytola, with additional actual half-integer matrix implementation copyright (c) 2026; Apache 2.0. Finite-support and contraction architecture: VirasoroProject 5ff4245383b2cdd4eea7a0524bc1274c32041eb4 through PolynomialFock bfd9ff0f15397a4fb933f36d701a60d325d84b08. Normal-product organization retains Scott Carnahan, vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. Classical sources: Dong-Nagatomo math/9808088v1 section 3.2, with rank/16 on page 19 attributed there to Frenkel-Lepowsky-Meurman; Bakalov-Kac math/0402315v1 (4.4) and (4.23)-(4.38). No mathematical novelty is asserted.

This is an algebraic identification on the constructed actual tensor module. It does not construct analytic completions, a full conformal twisted module, a completed moonshine VOA/CFT, anomaly or fusion structures, string dynamics, geometric reconstruction or AdS/CFT. The complete programme remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.correctedField_omega`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_charged_zero_identity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal.current_identity_coefficient`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalState](LatticeActualConformalState.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](LatticeHalfFockOriginalTranslation.md)
