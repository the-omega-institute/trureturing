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

**Theorem 1.2 (All spectral functions intertwine).**

Lean statement: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

Under the norm-saturated contraction comparison, equality of every positive-shift resolvent quadratic form forces f(A) Vb = V f(B)b for every real function f. Repeated eigenvalues are grouped and finite rational residues determine each eigenspace coefficient. No global continuity of f is required because the finite spectra are discrete. The theorem is used in the logarithm-to-Petz proof.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.cfc_shift_inverse`
- Truth anchor: `D5/S3/Quantum/Divergence/ResolventFunctionalRigidity.zero_resolvent_defects_force_functional_intertwining`
- Dependency: [D5/S3/Quantum/Divergence/ResolventDefectRigidity](ResolventDefectRigidity.md)
