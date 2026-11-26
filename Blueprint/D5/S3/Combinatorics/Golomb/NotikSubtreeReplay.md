# Composing Golomb subtree certificates

## Abstract

Checked subtree certificates compose in branch order.

**Definition 1.1 (A subtree passes both checks at its inherited path).**

Lean statement: `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.SubtreeCertificate`

*Formalization.* `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.SubtreeCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A certificate for a target, static rows, relation witnesses, inherited path, tree and leaf table gives two equations. The bound check returns true and the equality check consumes the full table, returning an empty remainder.

**Theorem 1.2 (Child certificates compose at a branch).**

Lean statement: `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.branch`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.branch` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the branch relation has a witness, the negative branch row extends the inherited path for the left child and the positive row extends it for the right child. Given certificates for the two children on these paths, the parent has a certificate with the left leaf table followed by the right leaf table. Appending entries to a successfully covered table leaves the appended entries untouched, so the left check hands exactly the right table to the right check.

## References

- Truth anchor: `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.SubtreeCertificate`
- Truth anchor: `D5/S3/Combinatorics/Golomb/NotikSubtreeReplay.branch`
- Dependency: [D5/S3/Combinatorics/Golomb/EqualityReplay](EqualityReplay.md)
