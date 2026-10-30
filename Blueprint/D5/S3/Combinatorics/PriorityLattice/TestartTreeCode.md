# Increasing Trees and Cycle Insertion

## Abstract

Native increasing-tree parent codes, maximum-label cycle insertion and exact excedance transport.

**Definition 1.1 (Positive-label parent codes).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.ParentCode`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.ParentCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Vertex v represents label v+1; its value is the strictly smaller parent label.

**Definition 1.2 (Existing unordered native trees).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.NativeTree`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.NativeTree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

The source carrier is the existing IntervalForest tree subtype on labels 0 through n. Its single connected component makes the interval condition automatic; no sibling order is stored.

**Definition 1.3 (Split off the maximum).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.splitCode`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.splitCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Apply the upstream dependent tuple equivalence to separate the largest vertex parent.

**Definition 1.4 (Insert a new maximum).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertEquiv`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

The upstream option-permutation decomposition is inverted so the new maximum follows its parent. Parent zero creates a singleton cycle.

**Theorem 1.5 (The actual inserted permutation).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insert_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insert_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

The insertion equivalence is computed by the upstream option swap and option congruence, so it inserts after the selected positive parent and creates a singleton for parent zero.

**Theorem 1.6 (Actual native parent incidence).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.native_parent_code`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.native_parent_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Decoding a parent code through the existing treeEquivCode gives exactly its stored parent at every positive native vertex. This is an equality of actual parent fields, rather than a cardinality identification.

**Definition 1.7 (Recursive cycle insertion).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.codeEquiv`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.codeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Iterate maximum-label insertion over all parent codes, including size zero.

**Definition 1.8 (Native carrier interface).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.nativeEquiv`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.nativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Compose the existing treeEquivCode with insertion. The parent-incidence bridge verifies the actual parent field, and the private statistic identifies each positive internal label with a strict excedance position.

**Definition 1.9 (Positive internal labels).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.HasChild`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.HasChild` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

A positive label is internal exactly when it occurs as a parent value.

**Definition 1.10 (Native incidence).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.Internal`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.Internal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

A native vertex is internal exactly when some vertex has it as parent.

**Definition 1.11 (Position reflection).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.reflectPositions`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.reflectPositions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Reverse the first n-1 positions and fix the last; for n=1 this is the identity.

**Definition 1.12 (The fixed D operation).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Compose position reflection, the supplied permutation, and full value reflection. In positive coordinates this is D(s)(i)=n+1-s(n-i) for i<n and D(s)(n)=n+1-s(n). The private proofs establish involutivity and strict-excedance transport, including fixed points.

**Theorem 1.13 (Positive-label formula for D).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

For every position, reflectPositions sends positive i to n-i when i<n and fixes n. The output positive value is n+1 minus the supplied permutation value at that reflected position. The theorem includes size one and the last position.

**Definition 1.14 (The source restricted tree family).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.TreeClass`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.TreeClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Internal vertex labels are exactly 0 through a-1 in the native tree on 0 through a+b-1. All other labels are leaves.

**Definition 1.15 (The published strict-excedance family).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.PermClass`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.PermClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Permutations of a+b-1 positive labels have strict excedance positions exactly 1 through b-1. Fixed points are allowed.

**Definition 1.16 (Restricted insertion equivalence).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertionClassEquiv`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertionClassEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

For every positive a and b, the insertion implementation restricts to an equivalence between the exact native internal-label class and the published permutation class. This equivalence supplies the restricted inverse laws used by TestartTraversal.result. The latter also proves the literal DFS and minimum-first reconstruction specifications of its algorithms.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.HasChild`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.Internal`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.NativeTree`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.ParentCode`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.PermClass`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.TreeClass`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.codeEquiv`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.dual_formula`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertEquiv`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insert_apply`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.insertionClassEquiv`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.nativeEquiv`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.native_parent_code`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.reflectPositions`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTreeCode.splitCode`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/IntervalForestBasic](IntervalForestBasic.md)
