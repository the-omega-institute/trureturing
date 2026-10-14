# Actual Finite Contact Graft Iteration

## Abstract

Earned actual b contacts let all remaining complete stars be grafted sequentially onto the two-star core, producing a Hamilton cycle on the full F2 union.

PartialDomain(m,k) is the actual CoreDomain together with all complete SupplierStar(contactAnchor(j)) for j in Fin(m-2) with j<k. F2Domain(m) is PartialDomain(m,m-2), so it includes every tuple (1,...,j+1,m,j+2,...,m-1,0) from the concrete remaining family. The induced graph has the actual prefix-reversal generators a, b, c; the domain is defined by deletion membership rather than by the support of a chosen walk.

**Theorem 1.1 (All Actual Remaining Contacts Produce a Complete F2 Hamilton Cycle).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists base \in \mathrm{Vertices}\left(\mathrm{F2Domain}\left(m\right)\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{domainGraph}\left(\mathrm{F2Domain}\left(m\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeContactIteration.native_f2_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least four, there is a genuine Hamilton cycle on the native three-generator graph induced on the independently specified full F2 union. The statement assumes neither a matching nor the occurrence of any contact edge. Those edges are earned along the same cycle construction.

Start with the existing actual two-star core Hamilton cycle. Both endpoints of each contact b edge lie in its contact circle, hence in the core. The concrete contact classification excludes that edge from CoreDeletedEdge. Thus the existing core inventory places every pending contact edge in the initial cycle. This establishes the finite induction's edge invariant.

At step k, the next complete star meets PartialDomain(m,k) exactly in its contact circle: the core intersection has already been classified, and the earlier contact stars are pairwise disjoint. The pending-edge invariant supplies the actual b edge at index k, so native one-contact E grafting constructs a Hamilton cycle on PartialDomain(m,k+1).

Every later contact edge differs from the edge just opened. Equality of undirected edges would identify a vertex from two disjoint complete contact stars. Old-edge retention therefore carries all later contacts into this same new cycle. Iterating through m-2 actual grafts exhausts the finite family and yields the complete F2 witness.

This result constructs the actual finite F2 layer. It does not identify the full graph with that layer or prove the later marked-path recombination and all-size recursive Hamiltonicity conclusion. An exact arbitrary-edge inventory for the whole iterated cycle is a further obligation.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeContactIteration.native_f2_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeStarContacts](NativeStarContacts.md)
