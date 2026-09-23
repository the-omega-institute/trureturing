# The component correction identity

## Abstract

Let H be a finite family of subsets of an n-element vertex type, m=card(H), and P=binom(n,2). The side predicate is defined for every H. Under DUF and the cap of at most four neighbors per ground pair, each four-edge fiber F(S) with card(S)=4 determines one center/support component, and each counted component has exactly two sides.

**Definition 1.1 (One side of a block).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponentCounts.blockSide`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFComponentCounts.blockSide` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S is a side of (c,U) when some opposite four-set A forms a complete block (c,A,S) in H and U=A union S. The underlying block identity is (c,U); under the cap, it identifies a link component.

**Theorem 1.2 (Two fibers per component).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponentCounts.reciprocal_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponentCounts.reciprocal_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For DUF H with the cap, b=2B. The proof counts actual side-component incidences in both directions. Exact neighborhoods show that any two bipartitions of one support have the same two sides up to interchange.

**Theorem 1.3 (The full counting identity).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponentCounts.component_counting`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponentCounts.component_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a three-uniform DUF family of maximum pair codegree at most four, q4+a=h4+4B and 8B<=h4. Moreover 6m+a+q2+2q1+3q0+h1+3h0=6P+4B, while 21m+10h0+3h1+h3<=22P. If m>P, integrality forces B>=2 and h4>=16. No global charging inequality or unrestricted-codegree conclusion is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponentCounts.blockSide`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponentCounts.component_counting`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponentCounts.reciprocal_count`
- Dependency: [D5/S3/Combinatorics/Graph/DUFComponents](DUFComponents.md)
