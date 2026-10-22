# Physical slices reconstruct the original native normal words

## Abstract

Physical slices reconstruct the original native normal words

physicalSlice samples the original cover coefficient at twice the physical exponent minus the retained shift. physicalJet is the original jetScalar times tensorCurrent at every signed integer mode. Pointwise lower truncation follows from the existing current cutoff and the actual native field order, without a source or target occupation cutoff.

**Theorem 1.1 (The original negative-mode split is exactly the physical normal-product split).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_normalInsertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_normalInsertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The two original natural-offset sums are compared term by term with the actual normalMinusOne coefficients. The native jetShift retains its factor two times the frequency plus three; the physical convolution has the rest mode n minus m minus one. The resulting external cover shift is two times the frequency plus one, not plus three. There is no exponent-sign replacement of the original m less than zero split and no exchange of infinite sums.

**Theorem 1.2 (Every original normal word is the sum of two shifted physical lifts).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.normalWord_physical_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.normalWord_physical_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

wordShift is the sum over the actual indices of two times the frequency plus one. Normal insertion induction identifies each parity slice with the nested physical normal word. Integer division and the complementary even and odd remainder cases then reconstruct every native coefficient, including all negative exponents. This is a coefficient identity of the original normalWord, not a replacement state-field definition.

The original charged monodromy is consumed by physicalCharge_parity_mode: twice the parity slice is exactly the coefficient of A_a plus the parity sign times A_minus_a. Reconstruction also works directly with the half-sized slices and does not assume an all-state involution. Full twisted Jacobi and the string/AdS bridge remain open. Compiled mathematical identities do not alone provide four-slot escape admission.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.normalWord_physical_reconstruction`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_normalInsertion`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProductLocality](FieldNormalProductLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStateField](LatticeHalfFockAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](LatticeHalfFockChargedMonodromy.md)
