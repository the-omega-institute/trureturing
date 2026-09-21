# The exact triple forcing threshold

## Abstract

The exact triple forcing threshold

**Theorem 1.1 (The exact triple forcing threshold).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFTripleConclusion.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFTripleConclusion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any finite type and H any finite family of triples in V satisfying the disjoint-union-free condition. Let P be all two-element subsets of V. Define S as the pairs p in P with nonempty neighbors(H,p), and T as the pairs q in P with nonempty common(H,q). Then 2|H| is at most |S|+|T|, and |H| is at most binomial(|V|,2). S and T are these filtered ambient pair sets. There is no restriction on codegrees, isolates, graph sizes, or whether V and H are empty.

A four-distinct collision in H consists of four pairwise distinct actual members A,B,C,D with A disjoint from B, C disjoint from D, and A union B equal to C union D. For triple families, such a collision exists exactly when DUF fails. Disjointness and cancellation show that any nontrivial failure of uniqueness has all four members distinct; conversely a collision excludes both permissible pair identifications.

For each natural number n, dufTripleFamilies(n) is the finite set of all DUF subfamilies of the triples on Fin(n). Define M3(n) as the maximum of their cardinalities. This maximum is attained by an actual triple family, and every such DUF family has at most M3(n) members. Define collisionForcing(n,m) to mean that every actual triple family on Fin(n) with at least m members has a four-distinct collision. F3(n) is the least natural number with this forcing property, defined as the infimum of that subset of the naturals.

For every n, F3(n)=M3(n)+1. It is the least member of the forcing set, and collisionForcing(n,m) holds if and only if F3(n) is at most m. This includes n below three, where the maximum is zero and the forcing threshold is one. For n at least three, binomial(n-1,2)+1 is at most F3(n), and F3(n) is at most binomial(n,2)+1. The lower bound is supplied by the actual star family of all triples containing a fixed vertex.

The real-valued sequence F3(n)/binomial(n,2) tends to one as n tends to infinity. For n at least three, the bounding ratios are 1-2/n+2/(n(n-1)) and 1+2/(n(n-1)). Both tend to one, and the actual forcing ratio lies between them. Values at the finitely many zero denominators do not affect this limit.

To prove the upper bound, work with each actual properly three-colored local graph. On the full vertex set, the finite-set neighborhood is exactly neighborFinset, mixedness agrees, and the two potentials agree. Counts two through five of mixed vertices have potential at least two. The zero, one and at-least-six cases therefore show that potential below two forces a unique mixed vertex adjacent to a leaf whose whole color class is a singleton.

This obstruction places every member whose weight is below two in an actual marked internal group. On a nonempty selected set, the residual degree and singleton-leaf exclusion contradict the same obstruction, so its residual potential is at least two, including when the residual graph is empty. Thus every remaining score outside the internal union is at least two. Global balance yields twice the family cardinality as a lower bound for total reciprocal weight.

Double counting identifies that total weight exactly with |S|+|T|. The first contribution counts extensions of each supported pair with total reciprocal mass one. The second counts ordered neighbor pairs, whose two orientations cancel the factor one half. Each of S and T has at most binomial(|V|,2) members. These statements establish uniformity three only; the assertion for every fixed higher uniformity is outside this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFTripleConclusion.result`
- Dependency: [D5/S3/Combinatorics/Graph/DUFGlobalAllocation](DUFGlobalAllocation.md)
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorOuterCases](ThreeColorOuterCases.md)
- Dependency: [D5/S3/Combinatorics/Graph/ThreeColorSmallMixed](ThreeColorSmallMixed.md)
