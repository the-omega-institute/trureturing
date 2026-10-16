# Coverage and real cofactor soundness

## Abstract

Coverage and real cofactor soundness.

**Theorem 1.1 (Coverage and real cofactor soundness).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness.oriented_full_cofactor_in_catalog`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness.oriented_full_cofactor_in_catalog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support tables cover every increasing four-tuple of the nineteen column indices, equivalently every member of powersetCard 4. Opposite-sign and zero alternatives exclude nonzero nonnegative orientations. The remaining supplied equality gives a positive real multiple of an original catalog vector. The determinant cast identifies the integer checker cofactors with the actual real ordered full-row cofactors. Catalog projection recovers the original sixteen gap coordinates, including their alignment with the original ray labels. The minus-identity slack block supplies full row span and the exact equivalence with the three nonnegative boundary rows.

These statements concern real scalar spectra and finite cofactor certificates. Connecting the boundary inequalities to a physical APPT model, constructing an attaining state, and determining a purity supremum require additional results.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarConeSoundness.oriented_full_cofactor_in_catalog`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression](SpectrumCompression.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnOne](SupportColumnOne.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnTwo](SupportColumnTwo.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnZero](SupportColumnZero.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnsFiveEight](SupportColumnsFiveEight.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnsNineFifteen](SupportColumnsNineFifteen.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SupportColumnsThreeFour](SupportColumnsThreeFour.md)
