# Divided Source Translation for the Native Corrected-Field Detector

## Abstract

Divided Source Translation for the Native Corrected-Field Detector

Let D be even integral lattice data with unit Gram determinant, witnessed by hu. Take arbitrary actual twisted tensors R and S in ActualTensor D hu, and a source a in Carrier D. Write T for LatticeSugawaraConformal.translation D and B_e(a) for the detector with input R and test tensor S at signed doubled Hahn exponent e.

**Definition 1.1 (The corrected-field detector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Extract coefficient e of the original corrected field of a, apply it to R, and pair the result with S using ActualChargedAdjoint.actualForm. The resulting functional is complex-linear in a.

**Theorem 1.2 (Evaluation of the detector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_apply`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The value B_e(a) is actualForm D hu ((correctedField D hu a).coeff e R) S. The field coefficient acts on the first tensor and the bilinear form tests it against the second.

**Theorem 1.3 (Divided translation at every signed doubled exponent).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_divided_translation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_divided_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer e and natural h, B_(e − 2h)(T^h a) divided by h! equals binom(e/2, h) B_e(a), with the generalized binomial Ring.choose over the complex numbers. LatticeHalfFockOriginalTranslation.correctedField_translation_physical gives B_j(Ta) = ((j + 2)/2) B_(j + 2)(a) by bilinearity. Induction on h gives the falling product of e/2 − k over 0 ≤ k < h. This is the coefficient identity (1/h!) ∂_z^h z^(e/2) = binom(e/2, h) z^(e/2 − h) for formal half-integer powers. The complex binomial normalization follows from Ring.choose_eq_smul and descPochhammer_eval_eq_prod_range.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_apply`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeDetectorTranslation.detector_divided_translation`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](../../LatticeHalfFockOriginalTranslation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint](../ActualChargedAdjoint.md)
