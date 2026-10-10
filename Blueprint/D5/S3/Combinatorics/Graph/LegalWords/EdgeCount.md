# Counting legal-word toggle edges by deletion

## Abstract

For every natural length, the unordered Fibonacci cube edge count equals total occupation over legal words and the size-weighted sum of their actual counts.

A word is a Boolean function on Fin n. Its support in positions 1 through n contains i+1 exactly when the value at the zero-based position i is true. The existing predicate Adm says that no two consecutive positions are true. The existing legalWordGraph is the induced Boolean hypercube on these literal words: an unordered edge is a pair whose Hamming distance is one. Occupation is the sum of the Boolean values converted to natural numbers, hence the size of that same support.

**Definition 1.1 (The actual legal-word carrier).**

$$\forall n \in \mathbb{N},\; \mathrm{Legal}\left(n\right) = \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.Legal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Legal n is the subtype of Boolean functions on Fin n satisfying Adm. It includes the unique empty word when n is zero.

**Definition 1.2 (Counting occupation fibers).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \mathrm{supportCount}\left(n, k\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda b \in \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\}, \mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right) = k, \operatorname{Finset.univ}\left(\{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.supportCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

supportCount n k is the cardinality of the finite set of actual legal words of length n whose occupation is k. It is not an independently specified sequence. All counts use the same word carrier as the graph.

**Theorem 1.3 (Two counts of the same edges).**

$$\forall n \in \mathbb{N},\; \operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(\mathrm{legalWordGraph}\left(n\right)\right)\right) = \sum_{b: \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\}} (\mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right)) \land \sum_{b: \{w: \mathrm{Fin}\left(n\right) \to \mathrm{Bool} \mid \mathrm{Adm}\left(n, w\right)\}} (\mathrm{occupationCount}\left(\mathrm{val}\left(b\right)\right)) = \sum_{k: \operatorname{Finset.range}\left(\mathrm{div}\left(n + 1, 2\right) + 1\right)} (k \cdot \mathrm{supportCount}\left(n, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.edge_count` (`✓ std3`). ∎

*Citation.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

For every natural n, the cardinality of the native unordered edge finset equals the sum of occupation over all Legal n words. That same sum equals the sum of k times supportCount n k, for k from zero through the integer quotient of n+1 by two, inclusive. There are no additional count hypotheses.

Delete an occupied position from a legal word. Deletion preserves legality, changes exactly one coordinate, and reduces occupation by one. Two such deletion pairs cannot define the same unordered edge unless both the larger word and the deleted position agree: swapping the endpoints would force occupation to decrease in both directions. Conversely, a Hamming-one edge has a unique differing coordinate; its true endpoint and that coordinate recover the deletion pair. This bijection gives the first equality. Partitioning the same words by occupation gives the second. The existing sharp occupation bound ensures that all fibers lie within the stated cutoff.

At length zero, the deletion-pair type and the edge set are empty, and both occupation sums vanish. The binomial formula for individual fibers, the observation-kernel dimensions, and exact-sequence claims are outside this statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.Legal`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.edge_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/LegalWords/EdgeCount.supportCount`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWordDegree](../LegalWordDegree.md)
