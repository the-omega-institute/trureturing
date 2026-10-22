# Actual Charged First Descendant

## Abstract

Actual Charged First Descendant.

The literal first source oscillator is evaluated through the existing finite Corr, correctedPolynomial and Ytw, not by defining a replacement descendant field. All colour sums are finite; the charge and lattice rank are unrestricted.

**Theorem 1.1 (Charged first-oscillator correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.Corr_charged_first_oscillator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.Corr_charged_first_oscillator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every lattice, charge a and colour i, actual Corr of X(i,0) has exactly two coefficients: X(i,0) at shift zero and minus B(unit_i,a)/2 times the oscillator unit at shift one. The negative half is calculated from halfBinomial 1 in the existing insertion constructor. Corr_X_zero is not used.

**Theorem 1.2 (Actual field of the charged first oscillator).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.charged_first_descendant_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.charged_first_descendant_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The proved charged Corr evaluation is consumed by correctedPolynomial and Ytw. The existing normalPolynomial_X and normalPolynomial_one identify the two constructor terms. A shift of one increases the charged cover exponent by two.

**Theorem 1.3 (Finite colour-linear descendant expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Ytw linearity expands the literal sum over colours of h(i) times Finsupp.single a X(i,0). This is a consumed organizational helper, not new mathematical content.

**Theorem 1.4 (Coefficient of the literal descendant).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The coefficient on every ActualTensor equals the finite colour sum of physical normal insertions minus B(h,a)/2 times the existing charged coefficient at E+2. This coefficient feeds the signed-cut bridge; no alternative carrier or assumed module law is used.

These proofs are consumed by the signed-cut and original mixed-iterate modules. Kernel compilation is distinct from completed four-slot source admission. The Reg mirror contains typed obligations and a full dependent coefficient bridge; complete variation, sensitivity, observational dependence and structural source selection remain missing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.Corr_charged_first_oscillator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.charged_first_descendant_field`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFirstDescendant.originalFirstDescendant_field`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockAllStateField](LatticeHalfFockAllStateField.md)
