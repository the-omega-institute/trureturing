# IdealIntersectionSupport

## Abstract

Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.

The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.

**Definition 1.1 (Actual ideals and the support graph).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actualSupportIso`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actualSupportIso` (`✓ std3`).

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Each ideal of ZMod n corresponds to a divisor of n, then to its prime-exponent vector. Removing the bottom and top ideals removes precisely the zero and full divisor endpoints. The support of an exponent vector records the coordinates below their maximal exponents. Intersection of two ideals is nonzero exactly when the corresponding supports intersect; distinctness is included. This proves the graph isomorphism used by every spectral conclusion.

**Theorem 1.2 (Ideal intersection and divisor lcm).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.adj_iff_lcm`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.adj_iff_lcm` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The divisor of an intersection is the least common multiple. The zero ideal corresponds to n. Thus distinct nonzero proper ideals are adjacent exactly when their divisor lcm differs from n.

**Theorem 1.3 (Exact actual vertex count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actual_vertex_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actual_vertex_card` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For every nonempty finite family of distinct primes and every positive exponent vector, the actual graph has product of (k_i+1) minus two vertices. The subtraction removes the two actual ideal endpoints.

**Theorem 1.4 (Positive proper support-cell multiplicities).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.vertex_support_fiber_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.vertex_support_fiber_card` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A nonempty proper support S has product of k_i over S vertices. These fibers supply the exact weights of the quotient and ensure a nonzero support value has a nonzero graph lift.

**Theorem 1.5 (Universal vertices, including zero count).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_vertex_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_vertex_count` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The full-support cell has product of k_i minus one vertices. The omitted element is the zero-exponent endpoint. This count may be zero, including every squarefree exponent vector. No proof assumes a positive universal-vertex count.

**Theorem 1.6 (The universal join).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_iff_full_support`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_iff_full_support` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Full support is equivalent to being adjacent to every other vertex. Thus the actual graph is the join of its induced nonuniversal part with the complete graph on the full-support fiber, allowing the latter fiber to be empty.

**Theorem 1.7 (Connected active complement).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.activeComplement_connected`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.activeComplement_connected` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A proper nonempty support omits a coordinate and is disjoint from that coordinate singleton. Distinct singleton supports are mutually adjacent in the complement. These paths prove that deleting the universal vertices leaves a connected complement, with all exponents arbitrary.

**Theorem 1.8 (Exact weighted sum).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_sum` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Grouping actual exponent vertices by support gives the weighted sum formula when the support function vanishes on the two removed endpoints. The equal paired weights later give total vertex sum zero.

**Theorem 1.9 (Actual complement action).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_complement_intertwining`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_complement_intertwining` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Complement adjacency is disjointness of nonempty supports. Grouping the degree-minus-adjacency action by support gives the displayed support operator with the removed endpoint cells excluded. This proves the bridge rather than assuming a matrix model.

**Theorem 1.10 (Nonzero support lifts).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_nonzero` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Every nonempty proper cell has positive cardinality for positive exponents. A nonzero support value is therefore realized at a genuine graph vertex.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.activeComplement_connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actualSupportIso`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.actual_vertex_card`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.adj_iff_lcm`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_complement_intertwining`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_nonzero`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.support_lift_sum`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_iff_full_support`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.universal_vertex_count`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/IdealIntersectionSupport.vertex_support_fiber_card`
