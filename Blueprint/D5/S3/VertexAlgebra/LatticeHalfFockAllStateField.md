# Corrected Native State Fields

## Abstract

Finite correction is consumed by native Fock-normal fields on the full lattice carrier.

**Theorem 1.1 (The actual assignment consumes the order-independent correction).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_monomial_enumeration`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_monomial_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every source monomial and every enumeration of its repeated occurrences, the actual Ytw assignment equals the finite correction-coefficient sum feeding normalPolynomial. The correction permutation theorem is on this live proof path. This does not assert normalWord permutation invariance or full twisted Jacobi.

correctedPolynomial applies Corr to the actual ordinary oscillator polynomial, uses Finsupp.lsum to apply normalPolynomial to each supported correction coefficient, and shifts its cover exponent by twice the physical correction shift. Ytw then uses the actual charge Finsupp.lsum on the full original Carrier. Thus neither a replacement charged map nor an assumed twisted-module law is introduced.

Every constituent field is formed only after its statewise coefficient finiteness and lower truncation are proved. The construction uses D : LatticeData and native hu : IsUnit D.G.det, with no PosDef, Leech, rank24, eigenbasis or occupation-cutoff premise. The source monomial basis, finite correction family, actual tensor currents, ActualGround and existing chargedField are retained unchanged.

**Theorem 1.2 (Pure charged states recover the existing charged field).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual correction of the oscillator unit is supported only at shift zero. The actual normal polynomial selects exactly the existing chargedField. This constructor endpoint introduces no second charged map.

**Theorem 1.3 (The actual vacuum field is the identity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_vacuum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The zero-charge state with unit oscillator polynomial maps to the exact identity field, using the existing charged coefficient and its genuine ground representation.

**Theorem 1.4 (A neutral single source oscillator is the physical jet insertion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current_insertion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current_insertion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The neutral single-occurrence correction is unchanged. Its actual field is normalInsertion into the identity. This equality is consumed by exact native current recovery; it is not an independent novelty claim.

**Theorem 1.5 (The actual source currents recover the existing tensor currents).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For source oscillator (i,0), the coefficientwise physical normal-insertion proof identifies Ytw with the existing tensorCurrentField on the original ActualTensor. The sign split is by underlying current mode, not by cover exponent.

**Theorem 1.6 (Every arbitrary source state has an actual finite-minimum truncation bound).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_source_lower_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_source_lower_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The actual finite source charge support and correction-shift supports provide a finite set of intermediate native-field orders. Inserting zero makes its minimum defined even for the zero state. Subtracting twice the maximum ordinary source weighted degree gives a lower bound for Ytw on the chosen target vector. The universal Corr shift bound is consumed in the proof. This does not assert a flattened multi-index support estimate.

**Theorem 1.7 (The existing corrected assignment consumes arbitrary enumerations).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_enumerated_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_enumerated_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For every charge, correction shift and supported monomial, any permutation of its occurrence list gives the same actual Ytw. The existing Corr and shiftLinear are unchanged; normalPolynomial_enumerated_expansion is applied inside the actual constructor. Complex coefficients and repeated occurrences are retained. The correction source weight is k+1, not the target odd weight.

**Theorem 1.8 (Every corrected coefficient is its unfiltered native Fock-normal sum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_fock_normal_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_fock_normal_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The finite outer charge, correction-shift and monomial sums contain the genuine all-integer multi-index sum. Its full product is leftAction, the existing chargedCoefficient, then rightAction, with every actual jetScalar and native current retained. The charged exponent is e+2s+2sum(j)+sum(2k+3), precisely the source shift by 2s and jet exponent -2j-2k-3. flatTerm_finite proves pointwise finite support before normalSequence_flattened interchanges the nested sums. This consumes both finite singleton/pair correction and normalWord permutation invariance without an assumed module/Jacobi record or an alternate charged map.

Twisted Jacobi, physical all-state translation, sectorTranslation recurrences, ground monodromy and inverse-Gram stress identification remain separate obligations. Ward/locality/original-Q suppliers are not imported into this increment. Reg obligation aliases are not completed four-slot registrations; source admission and Scribe emission are separate from kernel compilation. Full moonshine, CFT, anomaly, fusion, string theory and AdS/CFT remain open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_charge`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_current_insertion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_enumerated_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_fock_normal_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_monomial_enumeration`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_source_lower_truncation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockAllStateField.Ytw_vacuum`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField](LatticeHalfFockFockNormalField.md)
