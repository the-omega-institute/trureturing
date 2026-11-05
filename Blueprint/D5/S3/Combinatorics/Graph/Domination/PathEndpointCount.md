# Path endpoints and the original restricted family

## Abstract

Path endpoints and the original restricted family

**Definition 1.1 (Restricted actual family).**

Lean statement: `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restrictedFamily`

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restrictedFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maximal independent subsets omitting at least one of the two endpoints. Complementation corresponds to a minimal vertex cover containing at least one endpoint.

**Theorem 1.2 (Both endpoints).**

$$\forall (n : \mathbb{N}), \operatorname{card}\left(\operatorname{bothFamily}\left(n + 4\right)\right) = \operatorname{count}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.both_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, the maximal independent subsets of a path of order n+4 containing both endpoints are in bijection with unrestricted maximal independent subsets of order n. The middle restriction and endpoint insertion are actual inverses, including the empty middle at n=0.

**Theorem 1.3 (Exact endpoint partition).**

$$\forall (n : \mathbb{N}), \operatorname{restrictedCount}\left(n + 4\right) + \operatorname{count}\left(n\right) = \operatorname{count}\left(n + 4\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restricted_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The allowed family and the forbidden endpoint family partition all subsets at every order n+4. This is a sum of actual cardinalities, without relying on extrapolation.

**Theorem 1.4 (The complete source zero prefix).**

$$(\operatorname{restrictedCount}\left(0\right) = 0) \land ((\operatorname{restrictedCount}\left(1\right) = 0) \land ((\operatorname{restrictedCount}\left(2\right) = 0) \land (\operatorname{restrictedCount}\left(3\right) = 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restricted_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restricted count is zero at orders zero, one and two, and one at order three. The order-three family is proved to be exactly the singleton family containing the subset {1}.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.both_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restrictedFamily`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restricted_complement`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/PathEndpointCount.restricted_initial`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/PathMaximalIndependentCount](PathMaximalIndependentCount.md)
