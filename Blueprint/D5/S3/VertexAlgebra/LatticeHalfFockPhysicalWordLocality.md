# Ordinary Dong applies to the actual physical normal words

## Abstract

Ordinary Dong applies to the actual physical normal words

**Theorem 1.1 (All physical normal words are mutually local).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality.physicalWord_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality.physicalWord_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The completed original charged coefficient physical locality is evaluated at the exact parity-slice exponents. Its doubled cover shifts become ordinary integer-mode shifts with killing order the absolute charge pairing. The jet/charge and jet/jet localities are separately proved on the same actual carrier. Two finite word inductions consume the existing normalMinusOne_locality theorem through FiniteFieldLocality.localNormal; its sum of the three input orders gives a genuine sufficient bound independent of every target vector.

physicalWord is constructed from actual lower-truncated integer fields. Existing normal-product pointwise support proofs justify Dong's residue interchanges. No all-state twisted locality or twisted module identity is assumed. The full original VOA/string/AdS objective remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalWordLocality.physicalWord_locality`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality](LatticeHalfFockPhysicalGeneratorLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality](LatticeHalfFockPhysicalLocality.md)
