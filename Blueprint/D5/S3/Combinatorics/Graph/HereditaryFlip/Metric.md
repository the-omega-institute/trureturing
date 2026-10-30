# Geodesics in hereditary finite-support flip graphs

## Abstract

For a hereditary family of finite subsets of any ambient type, one-coordinate flips give native graph distance equal to symmetric-difference cardinality. Its distance intervals are exactly the legal supports between intersection and union.

A hereditary family is closed under taking subsets. The ambient type need not be finite, the family need not be finite, and no uniform bound on support size is imposed. All vertices have finite support. The deletion and insertion argument is classical; the Fibonacci-cube instance and its isometric hypercube geometry belong to the background surveyed by Sandi Klavzar in Structure of Fibonacci cubes: a survey. The results here concern arbitrary hereditary families, without a claim of mathematical novelty.

**Definition 1.1 (The native flip graph).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.flipGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.flipGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

Vertices are finite sets belonging to F. Two vertices are adjacent exactly when their symmetric difference has cardinality one. Thus an edge removes or inserts one occupied coordinate. This definition uses no heredity assumption and no ambient finiteness assumption.

**Theorem 1.2 (Every walk pays for its endpoint differences).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.walk_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.walk_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

For every family F, every two vertices A and B, and every native walk p from A to B, the cardinality of the symmetric difference of A and B is at most the length of p. Induction on the walk applies the symmetric-difference triangle inclusion at its first edge, whose symmetric difference has cardinality one.

**Theorem 1.3 (An actual deletion and insertion walk).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.exists_shortest_walk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.exists_shortest_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

If F is hereditary, any two vertices A and B admit a native walk with length equal to the cardinality of their symmetric difference. For a subset S of T, finite-set induction constructs a walk from T to S: unless T equals S, choose an element of T outside S, erase it, and prepend this legal edge to the smaller walk. Lower closure supplies membership of every intermediate support. Apply this construction from both endpoints to their intersection, reverse the second walk, and append. The two lengths count the two disjoint endpoint differences.

**Theorem 1.4 (Connectedness includes an empty vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

If F is hereditary and contains the empty set, its flip graph is connected. The empty set supplies a vertex, and the constructed walks supply reachability for every pair. The singleton family containing only the empty support is included.

**Theorem 1.5 (Native shortest-walk distance).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.dist_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.dist_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

For a hereditary F and any occupied vertices A and B, the native SimpleGraph distance equals the cardinality of their symmetric difference. The constructed walk gives the upper bound and every walk obeys the lower bound. The existence of an endpoint implies empty-set membership by heredity, so connectedness justifies choosing a shortest native walk. This avoids relying on the zero value assigned to distance between unreachable vertices.

**Theorem 1.6 (Coordinate characterization of distance intervals).**

Lean statement: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.interval_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.interval_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sandi Klavzar (2013). *Structure of Fibonacci cubes: a survey*. DOI: [10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z). URL: <https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf>.

*Commentary.*

For vertices A, B and M in a hereditary family, dist(A,M) plus dist(M,B) equals dist(A,B) if and only if the intersection of A and B is contained in M and M is contained in their union. Inclusion-exclusion says the sum of the two symmetric-difference cardinalities equals the endpoint difference plus twice their intersection cardinality. Equality therefore forbids a coordinate from changing on both legs. Such a repeated change occurs precisely when M omits a common coordinate or includes a coordinate absent from both endpoints. Only M belonging to F is assumed; the whole Boolean interval need not lie in F.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.dist_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.exists_shortest_walk`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.flipGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.interval_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/HereditaryFlip/Metric.walk_lower_bound`
