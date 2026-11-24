# Sharp spectral values of the strict certificates

## Abstract

Sharp spectral values of the strict certificates

**Theorem 1.1 (Direct proportional columns in the original labels).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.direct_certificate_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.direct_certificate_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the deficits fit, a positive normalized weight vector satisfying the prescribed row masses gives an attained direct spectral maximum. Sorting the weights reindexes the rows together with their missing-label columns. Their multiplicities and total score are preserved on returning to the original labels.

**Theorem 1.2 (Complementary clipped columns in the original labels).**

Lean statement: `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.complement_certificate_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.complement_certificate_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive weights and normalized clipped columns with the stated row masses give an attained complementary spectral maximum. The allowed column sum is strictly decreasing at the level one, so each certified scale is the canonical one. This makes the ordering argument valid for every certificate satisfying the original-label equations.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.complement_certificate_maximum`
- Truth anchor: `D5/S3/Quantum/Measurement/Auric/StrictCertificateBudgets.direct_certificate_maximum`
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalBlockTraceCertificates](UnequalBlockTraceCertificates.md)
- Dependency: [D5/S3/Quantum/Measurement/Auric/UnequalPhysicalTargets](UnequalPhysicalTargets.md)
