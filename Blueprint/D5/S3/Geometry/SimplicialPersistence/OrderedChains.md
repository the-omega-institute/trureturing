# Ordered integer face chains

## Abstract

The full ordered integer face complex and its coproduct coordinates.

**Definition 1.1 (The full ordered face complex).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedChainComplex`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedChainComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite linearly ordered vertex type V and pre-abstract simplicial complex K, the degree p module is the coproduct of copies of the integers indexed by the actual faces with p+1 vertices. The boundary deletes each vertex with sign minus one to the number of smaller vertices. The complex retains every natural degree, including empty face sets and degrees above dimension. Its names and face and boundary definitions are the suppliers used by the coordinate-cover singular comparison.

**Theorem 1.2 (The ordinary boundary squares to zero).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedBoundary_squared`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedBoundary_squared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such V and K and every natural p, orderedBoundary at p+1 followed by orderedBoundary at p is zero. Reindex each signed deletion sum by its increasing enumeration. The existing rank_enumeration and double_deletion lemmas at TauCeti.OrderedCover give the signs and simplicial interchange; the existing TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero cancels the double sum. No square-zero law is assumed.

**Definition 1.3 (Integer coordinates in every face degree).**

Lean statement: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.coordinates`

*Formalization.* `D5/S3/Geometry/SimplicialPersistence/OrderedChains.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite linearly ordered vertex type, every pre-abstract simplicial complex L and every natural degree p, coordinates maps the ordered integer face module to all integer functions on its actual p-faces. It is the canonical coproduct-to-direct-sum isomorphism followed by the finite direct-sum coordinate equivalence. A face generator has coefficient one at that face and zero elsewhere. Both the degree-zero heat operator and the all-degree real scalar extension use this same supplier.

## References

- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.coordinates`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedBoundary_squared`
- Truth anchor: `D5/S3/Geometry/SimplicialPersistence/OrderedChains.orderedChainComplex`
- Dependency: [D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover](../../Topology/TauCeti/Algebra/Homology/OrderedCechCover.md)
