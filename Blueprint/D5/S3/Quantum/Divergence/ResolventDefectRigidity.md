# Resolvent defect identity and coercive rigidity

## Abstract

Resolvent defect identity and coercive rigidity.

**Theorem 1.1 (Norm-saturated contraction defect).**

Lean statement: `D5/S3/Quantum/Divergence/ResolventDefectRigidity.resolvent_defect_identity_and_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ResolventDefectRigidity.resolvent_defect_identity_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For positive semidefinite finite complex matrices A and B, a contraction V with V* A V <= B, a vector b with norm saturation ||V b|| = ||b||, and every positive shift t, the resolvent scalar gap is the sum of two actual positive quadratic defects. It bounds t times the squared intertwining defect. Zero gap is equivalent to vanishing of both the vector defect and comparison defect. Norm saturation is a required hypothesis, not inferred from mere contractivity. This helper is consumed by the functional and logarithmic rigidity chain leading to actual Petz recovery; it claims no independent new theorem beyond that live derivation.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ResolventDefectRigidity.resolvent_defect_identity_and_bound`
