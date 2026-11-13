# SevenBitSpreadCompletion

## Abstract

Unique completion of every original eight-member partial spread.

**Theorem 1.1 (Entire even hyperplane).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.orthogonal_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.orthogonal_seven` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

All seven-point orthogonal sets in the original full even hyperplane are Lagrangians. The ordinary kernel check covers every compatible extension through the generic include-or-omit soundness theorem. It includes XOR closure and all original hyperplane intersection counts; it does not sample a spread.

**Theorem 1.2 (Unique actual ninth Lagrangian).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every eight disjoint full Lagrangians, the seven actual holes are the unique disjoint ninth completion. The conclusion returns the entire coordinate Submodule, exact carrier, finrank three and vanishing pairing on all its vectors. It uses the universal point/hyperplane count, rather than an example or transitivity assumption. Exact n7 remains open and the paused nineteen-color case exclusions are not executed.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.orthogonal_seven`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SevenBitSpreadCompletion.result`
- Dependency: [D5/S3/Combinatorics/Orthogonality/PartialSpreadHoles](PartialSpreadHoles.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/SevenBitCapacity](SevenBitCapacity.md)
