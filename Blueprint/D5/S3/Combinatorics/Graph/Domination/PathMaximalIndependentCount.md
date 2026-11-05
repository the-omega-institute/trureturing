# Actual maximal independent subsets of finite paths

## Abstract

Actual maximal independent subsets of finite paths

**Definition 1.1 (The actual family).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.family`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The family filters the powerset of 0,...,n-1 by maximal independence in Mathlib's native pathGraph n. A compiled bridge identifies this with bounded independent closed domination.

**Theorem 1.2 (Exact local membership).**

$$\forall (n : \mathbb{N}), \forall (I : \operatorname{Finset}\left(\mathbb{N}\right)), (I \in \operatorname{family}\left(n\right)) \Leftrightarrow (\operatorname{Valid}\left(n, I\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.mem_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership is equivalent to the original bounded labels, no adjacent selected pair, and closed domination of every path label.

**Theorem 1.3 (Invertible head and tail maps).**

$$\forall (n : \mathbb{N}), \operatorname{count}\left(n + 3\right) = \operatorname{count}\left(n + 1\right) + \operatorname{count}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.count_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, M(n+3)=M(n+1)+M(n). The first branch inserts label 0 and shifts the tail by two. The other inserts label 1 and shifts by three. Reading the tail reconstructs the original subset; the branches are disjoint by membership of label 0.

**Theorem 1.4 (Singleton boundary witnesses).**

$$\forall (n : \mathbb{N}), \forall (t : \mathbb{N}), (t < n) \Rightarrow ((\forall (i : \mathbb{N}), (i < n) \Rightarrow ((i = t) \lor ((i + 1 = t) \lor (t + 1 = i)))) \Rightarrow (\operatorname{Valid}\left(n, \left\{t\right\}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.valid_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n and t<n, if every label is t or adjacent to t then the singleton t satisfies Valid n. This helper is consumed by the exact short-path and endpoint boundary proofs.

**Theorem 1.5 (All short path boundaries).**

$$(\operatorname{count}\left(0\right) = 1) \land ((\operatorname{count}\left(1\right) = 1) \land (\operatorname{count}\left(2\right) = 2))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.count_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty path has one maximal independent subset, the one-vertex path has one, and the two-vertex path has two. These auxiliary paths do not introduce graph cases below the source order three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.count_initial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.count_recurrence`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.family`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.mem_family`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount.valid_singleton`
