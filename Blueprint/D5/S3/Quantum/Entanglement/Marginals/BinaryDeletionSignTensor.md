# Integer coefficients with zero one-site deletions

## Abstract

An integer witness for each ordered bit pattern, with vanishing one-site deletions.

**Theorem 1.1 (Cancellation at any site).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.deleteSite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.deleteSite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pattern at a site records agreement or one of the two ordered differences. An agreement contributes +1 at 00 and −1 at 11. A difference contributes +1 at its indicated pair. All other local coefficients are zero. When both Boolean words have the pattern’s length, the coefficient is the product of their local coefficients.

Split a pattern at the site to be deleted. In the two remaining words, the prefixes before that site have the corresponding prefix length. Reinsert zero in both words and then reinsert one. The two integer coefficients sum to zero. At the deleted site, the local diagonal coefficients are opposites. Reinstating each earlier site multiplies both by the same sign.

**Theorem 1.2 (A nonzero entry).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.actualEntry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.actualEntry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite pattern, choose the indicated ordered bits at differing positions and zero in both words at agreement positions. Every local coefficient is +1, so the resulting coefficient is +1.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.actualEntry`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSignTensor.deleteSite`
