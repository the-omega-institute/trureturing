# Allowed entries in the deletion kernel

## Abstract

Support of binary matrices in the common kernel of one-site deletion.

**Theorem 1.1 (Exact support criterion).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSupport.survives_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSupport.survives_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work on a finite set of sites. Preserve the two ordered bits wherever the selected words differ. Where they agree, allow their common bit to vary. A matrix supported on a chosen set of allowed words can have a nonzero entry at the selected pair and vanish under every one-site deletion exactly when both words remain allowed for every choice of the common bits.

The deletion equation gives opposite entries when the common bit changes. Inducting over changed coordinates propagates a nonzero entry to all choices of the common bits. Conversely assign a sign according to the parity of the occupied common bits and set the other entries to zero. Deleting a differing bit gives zero in both summands. Deleting a common bit cancels the opposite signs.

The following prose counterexample shows why the finite-site hypothesis matters. On an infinite site set, allow just the words with finitely many occupied sites. Take the diagonal matrix whose permitted entries are one for even occupation and minus one for odd occupation. All deletion sums cancel. The all-zero entry survives, although the all-one word has the same differing-coordinate pattern and is forbidden.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionSupport.survives_iff`
