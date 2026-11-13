# Full actual submodules and source criteria

## Abstract

Complete kernel/projection/placement geometry of the received orthogonality result.

**Theorem 1.1 (Full kernel/projection dimension).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.finrank_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.finrank_split` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The actual first-kernel and complete second projection recover the dimension of every split submodule by a proved kernel equivalence and rank-nullity.

**Definition 1.2 (Actual first-summand intersection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The pullback along the first inclusion is the kernel part K of every actual submodule.

**Definition 1.3 (Actual second projection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The image under the second projection is the full projection P.

**Theorem 1.4 (The uniquely determined quotient map).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.exists_unique_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.exists_unique_lift` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every submodule U determines exactly one linear f:P -> A/K; membership of (a,s) is equivalent to a mod K=f(s). A linear right inverse of the actual projection constructs f, including zero and full fibers.

**Definition 1.5 (All reconstructed submodules).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The carrier consists of all (a,s) with s in P and a mod K=f(s). It imposes no independent reconstruction premise.

**Theorem 1.6 (Exact recovered intersection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel_liftSpace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel_liftSpace` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every arbitrary full placement map recovers precisely its specified K.

**Theorem 1.7 (Exact recovered projection).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange_liftSpace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange_liftSpace` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Surjectivity of the quotient supplies every projection vector, without removing degenerate fibers.

**Theorem 1.8 (Full reconstruction).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.reconstruction` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The quotient map reconstructs every vector of the original entire submodule, and is unique.

**Theorem 1.9 (Distinct placements remain distinct).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace_injective` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Full quotient-valued linear maps give distinct actual submodules.

**Definition 1.10 (The entire fixed-profile fiber).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftEquiv`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

All linear maps P -> A/K are equivalent to all submodules with the exact prescribed first kernel and second image.

**Theorem 1.11 (Intersection with the complement).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondKernel_liftSpace`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondKernel_liftSpace` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The second-summand intersection is precisely the subtype image of ker(f).

**Theorem 1.12 (The complete bilinear X/Y/Z criterion).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.orthogonal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.orthogonal_iff` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

For every field, two arbitrary complementary spaces and every bilinear form vanishing on the first summand, full orthogonality is equivalent to the two cross-kernel pairings and the complete placement pairing. All representatives are full linear lifts, and zero-dimensional cases remain included.

**Theorem 1.13 (Exact full finite-field count).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.fiber_card` (`✓ std3`). ∎

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Over every finite field, count every submodule in the fixed K/P fiber by |F|^(dim(P)*(dim(A)-dim(K))). The actual lift equivalence and linear-map dimension formula prove the count.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.exists_unique_lift`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.fiber_card`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.finrank_split`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.firstKernel_liftSpace`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftEquiv`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.liftSpace_injective`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.orthogonal_iff`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondKernel_liftSpace`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SplitSubmoduleLift.secondRange_liftSpace`
