# Logarithm equality forces full finite spectral rigidity

## Abstract

Logarithm equality forces full finite spectral rigidity.

**Theorem 1.1 (From a scalar log equality to all spectral functions).**

Lean statement: `D5/S3/Quantum/Divergence/LogEqualityResolventRigidity.log_equality_forces_functional_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/LogEqualityResolventRigidity.log_equality_forces_functional_intertwining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For strictly positive finite complex A and B, V* V <= I and V* A V <= B, retain the distinguished-vector norm saturation hypothesis. Equality of the actual logarithm quadratic forms then forces f(A) Vb = V f(B)b for every real f. The proof differentiates the finite shifted-log difference, uses the nonnegative resolvent defect and its zero limit at infinity, and then finite spectral rigidity. This implication is a live ingredient of the supported Petz equality theorem, not an equality assumption disguised as recovery.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/LogEqualityResolventRigidity.log_equality_forces_functional_intertwining`
- Dependency: [D5/S3/Quantum/Divergence/ResolventFunctionalRigidity](ResolventFunctionalRigidity.md)
