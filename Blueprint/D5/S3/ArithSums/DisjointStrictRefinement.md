# Disjoint Strict Refinement: A384350 and A384318

## Abstract

A finite positive set admits a nontrivial disjoint strict partition family exactly when one member is a sum of distinct positive nonmembers.

A strict integer partition is represented by a finite set of positive parts. A family assigns one block to every member of S, with that member as its sum. Blocks for different members must be disjoint. NontrivialDisjointRefinement means at least one block differs from the singleton of its member; values of the block function outside S do not enter this predicate.

**Theorem 1.1 (A changed family exists exactly when an outside sum exists).**

$$\forall S \in Finset\left(\mathbb{N}\right),\; \left(\forall t \in \mathbb{N},\; t \in S \Rightarrow 0 < t\right) \Rightarrow \left(NontrivialDisjointRefinement\left(S\right) \Leftrightarrow \left(\exists s \in \mathbb{N},\; s \in S \land \left(\exists T \in Finset\left(\mathbb{N}\right),\; \left(\forall t \in \mathbb{N},\; t \in T \Rightarrow 0 < t\right) \land \left(Disjoint\left(T, S\right) \land sum\left(T, id\right) = s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/DisjointStrictRefinement.nontrivial_disjoint_refinement_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2025). *OEIS A384350 and A384318 — disjoint strict partition families*. URL: <https://oeis.org/A384350>.

*Commentary.*

Choose the smallest member whose block has changed. Each part of this block is strictly smaller than its sum: equality would force every other positive summand to disappear. If a part were in S, minimality would leave its own singleton block unchanged, contradicting pairwise disjointness.

Conversely, replace the selected singleton by its partition into positive nonmembers and keep every other singleton. The new family is disjoint and the selected block has changed. The empty set is included: it cannot supply a changed member.

The same pointwise criterion applies when S ranges over subsets of an initial interval (A384350) or over strict partitions of a total (A384318). The cited entries state the question; the proof here is a repository derivation. No sequence coefficient computation is part of this theorem.

## References

- Truth anchor: `D5/S3/ArithSums/DisjointStrictRefinement.nontrivial_disjoint_refinement_iff`
