# Exact integer polyline enumeration

## Abstract

Corner lists define the complete integer route, including every endpoint and zero-length segment.

A point is an integer pair. Each segment has Manhattan length L. Its prefix lists step(a,b,i) for i=0,...,L-1, and the final corner is retained once. For axis-aligned segments this is the same route as retaining the initial point and then appending steps 1,...,L of each segment.

**Theorem 1.1 (Sampling agrees with the full expanded list).**

$$\forall p \in \operatorname{List}\left(\mathrm{Point}\right),\; \forall i \in \mathrm{Nat},\; \operatorname{sample}\left(p, i\right) = \operatorname{getD}\left(\operatorname{getElemOptional}\left(\operatorname{expand}\left(p\right), i\right), \operatorname{Pair}\left(0, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.sample_eq_getD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every corner list p and natural index i, the recursive sampler equals the optional i-th element of expand(p), defaulting to (0,0). It searches segment lengths rather than expanding the preceding points. No axis-alignment assumption is needed for this enumeration identity.

**Theorem 1.2 (The expansion has one more point than total segment length).**

$$\forall p \in \operatorname{List}\left(\mathrm{Point}\right),\; \left(\neg p = \mathrm{Nil}\right) \Rightarrow \operatorname{ListLength}\left(\operatorname{expand}\left(p\right)\right) = \operatorname{length}\left(p\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.length_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty p, expand(p).length = length(p)+1, where length(p) is the sum of Manhattan segment lengths. Zero-length segments add no prefix points.

**Theorem 1.3 (The two endpoint conventions agree exactly).**

$$\forall p \in \operatorname{List}\left(\mathrm{Point}\right),\; \operatorname{axisAligned}\left(p\right) \Rightarrow \operatorname{expand}\left(p\right) = \operatorname{verifierExpand}\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.expand_eq_verifier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every axis-aligned p, expand(p)=verifierExpand(p). The segment endpoint identity joins the left-closed prefixes into the initial-point/right-closed loop. This proves the semantics used to import the actual 1,283 routing corners, including detours and repeated consecutive corners. It supplies no geometric nonintersection or homology assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.expand_eq_verifier`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.length_expand`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/IntegerPolyline.sample_eq_getD`
- Dependency: [D5/S3/Combinatorics/Graph/Products/LatticeRouting](LatticeRouting.md)
