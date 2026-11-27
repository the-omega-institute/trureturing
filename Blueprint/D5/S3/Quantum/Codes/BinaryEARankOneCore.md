# The finite binary rank-one core obstruction

## Abstract

No normalized binary rank-one core of support eight, nine or ten meets the three-zero bound.

**Definition 1.1 (Existence of a normalized core).**

Lean statement: `D5/S3/Quantum/Codes/BinaryEARankOneCore.claim`

*Formalization.* `D5/S3/Quantum/Codes/BinaryEARankOneCore.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A core has four head sites and m tail sites, with m between four and six. Its radical X and quotient Z generators are in systematic form [I | A] and [I | R]. The tail of A is stored as a nondecreasing list of nonzero four-bit column masks. The binary Gram condition AAᵀ = I is stored as the upper triangle with its diagonal first. Orthogonality to the radical gives ARᵀ = I. The X and Z tails preserve binary addition, and the representative for each quotient word has X-head zero and Z-head equal to that word. For every nonzero quotient word and every radical translate, at most three coordinates have both their X and Z bits zero.

**Theorem 1.2 (Exclusion on eight through ten support sites).**

Lean statement: `D5/S3/Quantum/Codes/BinaryEARankOneCore.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Codes/BinaryEARankOneCore.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Enumerate sorted tail columns with Gram signature equal to the identity. The required diagonal determines the last column. For the first three head basis words, enumerate the Z-tail masks with their required syndromes. For each tested head word and its Z tail, keep the X tails that pass the zero-count test for all 16 radical translates.

Check X basis images against their allowed lists and test each determined sum against the list for that sum. The seven nonzero words in the span of the first three basis words suffice. Every normalized core induces these basis images by restriction and respects each sum by linearity. Lean evaluates the finite search to false for each of the three lengths.

Application to an original code requires a common systematic head for the radical and the Z projection, the binary Gram identity for the radical X tail, and a linear choice of representatives with X-head zero. The bound on zeros must hold on the retained support sites for every radical translate.

## References

- Truth anchor: `D5/S3/Quantum/Codes/BinaryEARankOneCore.claim`
- Truth anchor: `D5/S3/Quantum/Codes/BinaryEARankOneCore.result`
