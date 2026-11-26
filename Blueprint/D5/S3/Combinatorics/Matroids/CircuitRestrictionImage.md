# The integral image of signed circuit restriction

## Abstract

The integral image of signed restriction to a spanning circuit with one extra ground vertex.

**Theorem 1.1 (Dual parallel-class sizes determine the image).**

Lean statement: `D5/S3/Combinatorics/Matroids/CircuitRestrictionImage.exists_topCycle_signedRestriction_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/CircuitRestrictionImage.exists_topCycle_signedRestriction_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a spanning circuit of a matroid on a finite ordered carrier. Suppose its ground is the disjoint union of K and one vertex x. Pair a top integral cycle with the oriented augmented boundary of K by summing its coefficients on the single-vertex deletions of K with the corresponding boundary signs. The integers attained are exactly the multiples of the gcd of the dual parallel-class sizes in K.

Each deletion of a vertex a of K is a primal base, so its complement is the dual base consisting of a and x. Thus the dual has rank two, all its ground vertices are nonloops, and x forms its own parallel class. On K the classes are the fibers of the dual singleton-closure map.

Assign an integer potential to each ground vertex, with potential zero at x. Place these integers on the facets of the ground simplex with the oriented incidence signs and take the augmented boundary. A coefficient omitting two vertices is their potential difference times an orientation sign. The two successive boundary operations give zero. The resulting chain is supported on primal bases exactly when the potentials agree on each dual parallel class.

Choose the common orientation factor so that the signed coefficient on each deletion of K equals the corresponding potential. For any top cycle these coefficients recover its potentials. The resulting boundary and the original cycle agree on faces omitting x. At a face containing x, the boundary equation after deleting x forces the remaining coefficient to agree.

Summing the potentials by class gives a sum of freely chosen integers weighted by the class sizes. Every such sum is divisible by their gcd, and the integer Bezout identity realizes every multiple. The augmented coordinates include the empty face when K is a singleton.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/CircuitRestrictionImage.exists_topCycle_signedRestriction_iff`
- Dependency: [D5/S3/Combinatorics/Matroids/OrderedCycleFactorization](OrderedCycleFactorization.md)
