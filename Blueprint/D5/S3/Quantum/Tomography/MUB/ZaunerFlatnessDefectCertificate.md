# Zauner Flatness Defect Certificate

## Abstract

Structural zeros give positive flatness-defect margins for canonical Zauner completions.

**Theorem 1.1 (A zero entry bounds the defect below).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.target_sq_le_entrywise_flatness_defect_of_zero_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.target_sq_le_entrywise_flatness_defect_of_zero_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex matrix on finite row and column types and a real target, one zero entry makes the sum of squared differences between entry squared norms and the target at least the square of the target.

**Theorem 1.2 (A nonzero target gives positive defect).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.entrywise_flatness_defect_pos_of_zero_entry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.entrywise_flatness_defect_pos_of_zero_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a complex matrix on finite row and column types, a nonzero real target and one zero entry make the sum of squared differences between entry squared norms and the target strictly positive.

**Theorem 1.3 (The normalized defect is at least one thirty-sixth).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be a three-by-three complex matrix with F times its adjoint equal to the identity, and let x and x-prime be arbitrary complex triples. For one half of the product of the Zauner left factor for x with the adjoint of the left factor for x-prime, the sum of squared differences between entry squared norms and one-sixth is at least one thirty-sixth.

**Theorem 1.4 (The normalized transition cannot be flat).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_not_flat`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_not_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-by-three complex F with F times its adjoint equal to the identity and arbitrary complex triples x and x-prime, one half of the product of their Zauner left factors, with the second factor adjointed, cannot have every entry squared norm equal to one-sixth.

**Theorem 1.5 (A joint sum-of-squares exclusion certificate).**

Lean statement: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_exact_sos_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_exact_sos_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-by-three complex F satisfying the row unitary law and arbitrary complex triples x and x-prime, the half-scaled Zauner left-factor product with the second factor adjointed has defect at least one thirty-sixth relative to target one-sixth, and its entry squared norms are not all one-sixth. Both conclusions hold together.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.entrywise_flatness_defect_pos_of_zero_entry`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.target_sq_le_entrywise_flatness_defect_of_zero_entry`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_exact_sos_exclusion`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_defect_ge_one_div_thirty_six`
- Truth anchor: `D5/S3/Quantum/Tomography/MUB/ZaunerFlatnessDefectCertificate.zaunerCanonicalCompletion_normalized_not_flat`
- Dependency: [D5/S3/Quantum/Tomography/MUB/ComplexHadamardEntrywiseDefect](ComplexHadamardEntrywiseDefect.md)
- Dependency: [D5/S3/Quantum/Tomography/MUB/ZaunerCompletionFibre](ZaunerCompletionFibre.md)
