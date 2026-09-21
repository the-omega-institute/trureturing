# Finite Exhaustion and the Bounded-Run Union

## Abstract

Every finite Boolean word extends into a dense null union of closed run languages.

**Theorem 1.1 (The complete boundary for the identity bit readout).**

$$\operatorname{Boundary}(\operatorname{id})$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunUnion.bounded_run_union_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write K(k)=bounded(id,k), W(k,n)=language(id,k,n), and U=union(id). All lengths n are natural numbers including zero, and run bounds k are at least two. The ambient measure is the fair independent Bernoulli Borel probability on all infinite Boolean streams.

Every K(k) is closed and is strictly contained in K(k+1). Its image under the prefix map at length n is exactly W(k,n). If k>n, this language contains all words of length n. Increasing k preserves membership, and every truncation from n to m at most n preserves membership. Inclusions and truncations retain the same coordinates.

The union U is nonempty, dense, proper, and Borel measurable. Every finite prefix image of U is the full word space, and its closure is the full stream space. The zero stream belongs to U; the all-true stream does not. Zero-tail extensions realize every allowed word, including the empty word.

The maps prefixes and threadStream identify streams and coherent prefix families bijectively and continuously in both directions. Membership in K(k) is equivalent to membership of every prefix in W(k,n). Under this identification the union of fixed-bound inverse limits is U, and the inverse limit of the levelwise unions is the full stream space. The canonical comparison retains each thread, is injective, is not surjective, and reads back exactly the same stream.

The source of the comparison requires existence of one k at least two for all n. The target requires, for every n, existence of a k at least two; max(2,n+1) suffices. These are the two distinct quantifier orders, with the empty prefix present in both.

The aligned event B(k,m) has probability (1-2^(-k))^m, for every natural m, including zero. K(k) is a subset of B(k,m); this is an upper bound, since aligned blocks do not check all sliding windows. Reindexing disjoint coordinates and currying the product law give independent blocks, and a block's unique all-true word has probability 2^(-k).

The geometric bound tends to zero, so every K(k) has measure zero. Countable subadditivity gives measure zero for U. Its closure is the whole probability space and has measure one. Finite prefix surjectivity therefore does not imply positive ambient measure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunUnion.bounded_run_union_boundary`
- Dependency: [D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunSpace](BoundedRunSpace.md)
- Dependency: [D5/S3/ConceptDynamics/RegistrationWitnesses](../RegistrationWitnesses.md)
