# Resolvents determine finite spectral intertwining

## Abstract

Resolvents determine finite spectral intertwining.

**Theorem 1.1 (Shifted inverse as finite functional calculus).**

Lean statement: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.cfc_shift_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.cfc_shift_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For every positive shift and positive semidefinite finite complex matrix, the inverse of A+t I is the actual CFC of x -> 1/(x+t). This organizing helper is consumed by logarithmic rigidity.

**Theorem 1.2 (Finite positive samples determine the spectral calculus).**

Lean statement: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.finite_resolvent_defects_force_functional_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.finite_resolvent_defects_force_functional_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai and Milan Mosonyi (2017). *Different quantum f-divergences and the reversibility of quantum operations*. URL: <https://arxiv.org/abs/1604.03089v4>.

*Commentary.*

Let A and B be arbitrary finite positive semidefinite complex matrices and V a contraction with V* A V <= B. Suppose V preserves the norm of the distinguished vector b. If the actual resolvent quadratic defects vanish at an injective finite family of positive shifts, and the number of shifts is at least the number of distinct eigenvalues in the union of the two spectra, then f(A) Vb = V f(B)b for every real function f. The two matrix carriers and the sampling carrier have independent universes; empty carriers, repeated eigenvalues and zero eigenvalues remain in scope.

Group repeated spectral values before clearing the common resolvent denominator. The numerator has degree at most the number of distinct spectral sites minus one. Its distinct positive sample roots force it to vanish, and evaluation at each negative spectral site isolates its residue. The contraction defect identity supplies actual resolvent-vector equality; finite spectral expansion then supplies every f. No continuity of f and no recovery equation are assumed. The existing all-positive-shift theorem consumes this finite result in the live logarithm-to-Petz proof.

Hiai and Mosonyi's Theorem 3.18 identifies the related spectral-cardinality support condition for standard quantum f-divergence reversibility. This result supplies the finite spectral rigidity step. A representing measure, its support-to-defect bridge and the singular standard f-divergence boundary terms are separate obligations; this theorem does not establish the full f-divergence recovery equivalence.

**Theorem 1.3 (All spectral functions intertwine).**

Lean statement: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Under the norm-saturated contraction comparison, equality of every positive-shift resolvent quadratic form forces f(A) Vb = V f(B)b for every real function f. Repeated eigenvalues are grouped and finite rational residues determine each eigenspace coefficient. No global continuity of f is required because the finite spectra are discrete. The theorem is used in the logarithm-to-Petz proof.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.cfc_shift_inverse`
- Truth anchor: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.finite_resolvent_defects_force_functional_intertwining`
- Truth anchor: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining`
- Dependency: [D5/S3/Quantum/Divergence/ResolventDefectRigidity](ResolventDefectRigidity.md)
