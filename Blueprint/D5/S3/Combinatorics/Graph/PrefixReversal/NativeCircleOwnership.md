# Native Circle Ownership

## Abstract

The actual two T supplier stars intersect in exactly two core circles and their union has a unique complete circle owner.

**Definition 1.1 (The Literal Lower Noncore Ports).**

$$\forall m \in \mathrm{Nat},\; \forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{lowerPort}\left(j\right) = \mathrm{mul}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{val}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.lowerPort` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower port is the actual product a*c*(b*c)^j used by the T core and contact classification.

**Definition 1.2 (The Literal Upper Noncore Ports).**

$$\forall m \in \mathrm{Nat},\; \forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{upperPort}\left(j\right) = \mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{lowerPort}\left(j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.upperPort` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper port exchanges labels zero and m in the corresponding lower port.

**Theorem 1.3 (Next Label at an Actual Position).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall i \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{nextLabel}\left(z, \mathrm{apply}\left(z, i\right)\right) = \mathrm{apply}\left(z, \mathrm{mkFin}\left(\mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), 1\right), \mathrm{add}\left(m, 1\right)\right), \mathrm{add}\left(m, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_nextLabel_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic next label is the configuration evaluated at the successor position modulo m+1.

**Theorem 1.4 (Previous Label at an Actual Position).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall i \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{prevLabel}\left(z, \mathrm{apply}\left(z, i\right)\right) = \mathrm{apply}\left(z, \mathrm{mkFin}\left(\mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), m\right), \mathrm{add}\left(m, 1\right)\right), \mathrm{add}\left(m, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_prevLabel_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cyclic previous label is the configuration evaluated at the predecessor position modulo m+1.

**Theorem 1.5 (Every Prefix Rotation Power on Positions).**

$$\forall m \in \mathrm{Nat},\; 2 \le m \Rightarrow \left(\forall k \in \mathrm{Nat},\; \forall i \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{val}\left(\mathrm{apply}\left(\mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), k\right), i\right)\right) = \mathrm{ite}\left(\mathrm{val}\left(i\right) < m, \mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), k\right), m\right), \mathrm{val}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_bc_pow_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least two, each power of b*c rotates the first m positions modulo m and fixes the last position.

**Theorem 1.6 (The Actual Two-Reversal Port Coordinates).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{val}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), i\right)\right) = \mathrm{ite}\left(\mathrm{val}\left(i\right) < \mathrm{sub}\left(m, 1\right), \mathrm{add}\left(\mathrm{val}\left(i\right), 2\right), \mathrm{sub}\left(m, \mathrm{val}\left(i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_ac_apply_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three, the product a*c has the displayed pointwise position formula.

**Theorem 1.7 (Lower Port Coordinates).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall i \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{val}\left(i\right) < m \Rightarrow \mathrm{val}\left(\mathrm{apply}\left(\mathrm{lowerPort}\left(j\right), i\right)\right) = \mathrm{ite}\left(\mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), \mathrm{val}\left(j\right)\right), m\right) < \mathrm{sub}\left(m, 1\right), \mathrm{add}\left(\mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), \mathrm{val}\left(j\right)\right), m\right), 2\right), \mathrm{sub}\left(m, \mathrm{mod}\left(\mathrm{add}\left(\mathrm{val}\left(i\right), \mathrm{val}\left(j\right)\right), m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lowerPort_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three, each lower port has the displayed modular pointwise formula on positions below m.

**Theorem 1.8 (The Last Label Position in a Lower Port).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{apply}\left(\mathrm{lowerPort}\left(j\right), \mathrm{mkFin}\left(\mathrm{sub}\left(\mathrm{sub}\left(m, 2\right), \mathrm{val}\left(j\right)\right), \mathrm{add}\left(m, 1\right)\right)\right) = \mathrm{last}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_m_position` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, label m occurs at the explicitly computed position m-2-j.

**Theorem 1.9 (The Next Label at m in a Lower Port).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{val}\left(\mathrm{nextLabel}\left(\mathrm{lowerPort}\left(j\right), \mathrm{last}\left(m\right)\right)\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the cyclic next label of m in every lower noncore port is one.

**Theorem 1.10 (The Previous Label at m in a Lower Port).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{val}\left(\mathrm{prevLabel}\left(\mathrm{lowerPort}\left(j\right), \mathrm{last}\left(m\right)\right)\right) = \mathrm{sub}\left(m, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_prev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the cyclic previous label of m in every lower noncore port is m-1.

**Theorem 1.11 (The Lower Port Terminal Label).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{apply}\left(\mathrm{lowerPort}\left(j\right), \mathrm{last}\left(m\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, every lower noncore port ends with label zero.

**Theorem 1.12 (The Upper Port Terminal Label).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{apply}\left(\mathrm{upperPort}\left(j\right), \mathrm{last}\left(m\right)\right) = \mathrm{last}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_last` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, every upper noncore port ends with label m.

**Theorem 1.13 (The Next Label at m in an Upper Port).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{val}\left(\mathrm{nextLabel}\left(\mathrm{upperPort}\left(j\right), \mathrm{last}\left(m\right)\right)\right) = \mathrm{add}\left(\mathrm{val}\left(j\right), 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_next` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the cyclic next label of m in upper port j is j+2.

**Theorem 1.14 (The Previous Label at m in an Upper Port).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{val}\left(\mathrm{prevLabel}\left(\mathrm{upperPort}\left(j\right), \mathrm{last}\left(m\right)\right)\right) = \mathrm{ite}\left(\mathrm{val}\left(j\right) = 0, 1, \mathrm{add}\left(\mathrm{val}\left(j\right), 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_prev` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the cyclic previous label of m is one at j=0 and j+1 otherwise.

**Theorem 1.15 (Actual T Circle Owner Uniqueness).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \forall p \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \forall q \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \left(\mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(p\right), v\right) \land \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(q\right), v\right)\right) \Rightarrow p = q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_owner_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, two indexed T circle domains containing the same actual configuration have the same owner. This is consumed by the concrete contact edge classification.

The ownership argument compares actual tuple cycles. Rotation preserves both cyclic neighbours of every label and whole reversal exchanges next with previous. Existing coordinate equivalence then proves that two distinct insertion gaps cannot share a complete circle.

**Theorem 1.16 (Distinct Insertion Gaps Have Disjoint Circle Domains).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall i \in \mathrm{Fin}\left(m\right),\; \forall j \in \mathrm{Fin}\left(m\right),\; \left(\neg i = j\right) \Rightarrow \mathrm{Disjoint}\left(\mathrm{circleDomain}\left(\mathrm{gapAnchor}\left(z, i\right)\right), \mathrm{circleDomain}\left(\mathrm{gapAnchor}\left(z, j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an actual support statement for the F2 supplier decomposition. It uses the literal rotation/reversal quotient and does not infer ownership from a chosen path.

**Theorem 1.17 (The Deletion Star Is Exactly Its Complete Insertion-Gap Circles).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{Star}\left(\mathrm{apply}\left(z, \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(z\right), v\right) \Leftrightarrow \left(\exists i \in \mathrm{Fin}\left(m\right),\; \mathrm{Circle}\left(\mathrm{gapAnchor}\left(z, i\right), v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_star_circle_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least three, deleting the last label of the supplier tuple defines the whole star independently of any walk. A configuration belongs to that star exactly when it belongs to one of the m complete native gap circles. The existing star and circle coordinate equivalences prove both directions. Together with gap disjointness this gives the support partition used when grafting a new star onto an actual cycle through one contact circle.

**Theorem 1.18 (Circle Ownership Preserves the Unordered Cyclic Neighbours).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \forall x \in \mathrm{Fin}\left(\mathrm{add}\left(m, 1\right)\right),\; \mathrm{Circle}\left(z, v\right) \Rightarrow \left(\left(\mathrm{nextLabel}\left(v, x\right) = \mathrm{nextLabel}\left(z, x\right) \land \mathrm{prevLabel}\left(v, x\right) = \mathrm{prevLabel}\left(z, x\right)\right) \lor \left(\mathrm{nextLabel}\left(v, x\right) = \mathrm{prevLabel}\left(z, x\right) \land \mathrm{prevLabel}\left(v, x\right) = \mathrm{nextLabel}\left(z, x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual tuple rotations preserve next and previous labels, while whole reversal exchanges them. This invariant is the reusable boundary for cross-supplier ownership.

**Theorem 1.19 (The Two Native T Suppliers Have Disjoint Circle Domains).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall i \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{Disjoint}\left(\mathrm{circleDomain}\left(\mathrm{mul}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{val}\left(i\right)\right)\right)\right), \mathrm{circleDomain}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{pow}\left(\mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{val}\left(j\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_cross_circle_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four, the lower ports a*c*(bc)^i and the upper ports swap(0,last)*a*c*(bc)^j have disjoint complete rotation-and-reversal circle domains. At the label m, the lower neighbours are 1 and m-1, whereas the upper neighbours are j+2 and either 1 or j+1; the unordered-neighbour invariant then gives the arithmetic contradiction.

**Theorem 1.20 (The Two Complete Supplier Stars Intersect Exactly in Their Core Circles).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), v\right) \land \mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right)\right), v\right)\right) \Leftrightarrow \left(\mathrm{Circle}\left(1, v\right) \lor \mathrm{Circle}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_core_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two stars are defined independently by actual deletion of the label in the last position of a*c or swap(0,last)*a*c. Their intersection consists precisely of the complete circles based at the identity and swap(0,last). The two final insertion gaps are computed pointwise; all other shared ownership is excluded by the actual cross-circle theorem. This supplies the two core domains required by the F2 splice, without assuming a path partition.

**Theorem 1.21 (The Full Two-Star Union Has Exactly One Complete Circle Owner).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), v\right) \lor \mathrm{Star}\left(\mathrm{apply}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right), \mathrm{last}\left(m\right)\right), \mathrm{residualList}\left(\mathrm{mul}\left(\mathrm{swap}\left(0, \mathrm{last}\left(m\right)\right), \mathrm{mul}\left(\mathrm{a}\left(m\right), \mathrm{c}\left(m\right)\right)\right)\right), v\right)\right) \Leftrightarrow \left(\exists p \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(p\right), v\right) \land \left(\forall q \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(q\right), v\right) \Rightarrow q = p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut-owner index is Fin(m) plus Fin(m-2). Its first family comprises all lower insertion gaps, including the two shared cores; its second family comprises just the upper noncore ports. Every actual vertex in the independently specified union belongs to exactly one complete indexed circle. Full gap exhaustion supplies existence, and the earned core classification and disjointness supply uniqueness. This is a support partition; actual F2 path splicing and the higher marked-path induction remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.circle_neighbours`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.lowerPort`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_ac_apply_val`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_bc_pow_val`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_circle_gap_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lowerPort_val`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_last`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_m_position`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_next`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_lower_prev`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_nextLabel_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_prevLabel_apply`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_star_circle_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_owner_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_circle_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_core_intersection`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_t_cross_circle_disjoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_last`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_next`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.native_upper_prev`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership.upperPort`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement](NativeCircleComplement.md)
