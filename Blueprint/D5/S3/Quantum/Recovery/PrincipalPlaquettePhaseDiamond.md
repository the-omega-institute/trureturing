# A one-party plaquette obstruction for paired recovery

## Abstract

One party's plaquette phase bounds the native diamond error without a common quotient.

**Theorem 1.1 (Native one-party plaquette bound).**

Lean statement: `D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond.paired_one_party_native_diamond`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond.paired_one_party_native_diamond` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one selected pair of two-coordinate fibres, let theta be the first record's principal plaquette argument and p its quarter-angle cosine. The unhalved diamond error is at least p/2 minus 1/(4p), and at least one quarter minus theta squared over 32. A zero phase gives the quarter lower bound.

The opposite diagonal gauges preserve the tested entry products. Only the first record's phase is constrained and both cross blocks are contractions. There is no common quotient or entry-dominance hypothesis. The paired channel identity, target coefficient and selected fibre correspondence remain explicit.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PrincipalPlaquettePhaseDiamond.paired_one_party_native_diamond`
- Dependency: [D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond](PrincipalTrianglePhaseDiamond.md)
