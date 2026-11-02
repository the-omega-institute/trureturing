# Recovery of actual noncrossing partners

## Abstract

A cut noncrossing matching is determined by which endpoints open its pairs.

NCMatching(m) is the existing fixed-point-free involutive permutation of Fin m, with no alternating pairs. An opening is an endpoint k strictly smaller than its actual partner. The domain includes m=0; no existence or nonemptiness assumption is added.

**Definition 1.1 (An opening at a fixed cut).**

$$\forall m \in Nat,\; \forall M \in NCMatching(m),\; \forall k \in Fin(m),\; IsOpening(M, k) \Leftrightarrow k < partner(M, k)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.IsOpening` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The smaller endpoint opens its pair. This is a property of the actual partner permutation.

**Theorem 1.2 (Opening data recover every matched pair).**

$$\forall m \in Nat,\; \forall M \in NCMatching(m),\; \forall Q \in NCMatching(m),\; \left(\forall k \in Fin(m),\; IsOpening(M, k) \Leftrightarrow IsOpening(Q, k)\right) \Rightarrow partner(M) = partner(Q)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.partner_eq_of_openings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every frontier size and both noncrossing matchings on that same ordered frontier, agreement of the opening predicate forces equality of the full partner permutations. The proof uses the existing interior_closed theorem and induction on closing indices. If two partners of a closing differed, the intermediate opening would have closed earlier in one matching, contradicting agreement already established there. This is the pair-recovery fact used in the repository's rowmotion decoder argument.

For each n, CircularMatching(n) consists of an increasing embedding of six ranks into Fin(n+4), the existing NCMatching(6) partner permutation, and pairwise circular separation at least eight. Native site q is source site q+1. Ordinary means that every site has native value below n+2, excluding source sites n+3 and n+4. In endpoint data, a and b take values in Fin n, both are strictly decreasing, a(r) is at most b(r), and the indexed sites are a(0),a(1),a(2),b(0)+2,b(1)+2,b(2)+2. Every indexed pair must pass the circular distance test. Equality of occurrences fails it.

openingRanks and closingRanks sort the smaller and larger actual partners separately. start and finish transport those ranks to selected sites. The native decoder puts p in the decoded state exactly when start(M,reverse(row(p))) is at most column(p) and column(p)+2 is at most finish(M,reverse(row(p))). This is source row 4-j equal to [s_j,t_j-2], under the coordinate translation. The rank-paired endpoints are not required to be partners. endpointState is the actual union of its three intervals, and Separated(I) means existence of separated endpoint data with that exact actual set. No assumption that either family is nonempty is made.

**Theorem 1.3 (The ordinary decoder bijection).**

$$\forall n \in Nat,\; Injective(decode(n)) \land \left(\left(\forall M \in OrdinaryMatching(n),\; Separated(decode(M)) \land OrdConnected(decode(M))\right) \land \left(\forall I \in Set(Product(Fin(3), Fin(n))),\; Separated(I) \Rightarrow ExistsDecoder(n, I)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.ordinary_decoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, including the small parameters with empty families, decode is injective on the whole ordinary matching carrier, its values are separated interval-closed states, and every separated actual state is decoded by an ordinary matching. ExistsDecoder(n,I) means there exists M in OrdinaryMatching(n) with decode(M)=I. Injectivity recovers both the ordered site embedding and the complete actual partner permutation. The constructive inverse covers all five parenthesis orders while retaining independently sorted openings and closings. The result is the ordinary-bijection clause of the repository source's Theorem 2.5. It does not assert the decoder at nonordinary cuts, the literal toggle transition, or return reflection.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.IsOpening`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.ordinary_decoder`
- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionMatchingDecoder.partner_eq_of_openings`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionEndpointTransport](RowmotionEndpointTransport.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/OrderedMatchingIntervals](../PerfectMatchings/OrderedMatchingIntervals.md)
