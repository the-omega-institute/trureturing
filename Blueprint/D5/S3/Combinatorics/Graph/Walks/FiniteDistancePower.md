# Finite-path powers of disconnected graphs

## Abstract

Actual component supports and maximal independent Finsets retain their full spectra at every positive faithful power.

Fix a finite vertex type V and a simple graph G. The existing graphPower(G,d) joins distinct vertices only when their extended distance is at most d, so unreachable vertices are never joined. The frozen power(G,d), which uses natural distance, is used only on connected graphs. For a finite block map b:V to iota, assume every edge has both endpoints in the same block. Restriction keeps the actual subtype vertices, and assembly takes the disjoint union of their images in V. Empty blocks are harmless; in particular the results apply to arbitrary finite disjoint unions of nonempty graphs.

**Theorem 1.1 (The exact finite-walk semantics).**

$$\forall d \in \mathrm{Nat},\; \forall u \in V,\; \forall v \in V,\; \operatorname{Adj}\left(\operatorname{graphPower}\left(G, d\right), u, v\right) \Leftrightarrow \left(\operatorname{Distinct}\left(u, v\right) \land \left(\exists p \in \operatorname{Walk}\left(G, u, v\right),\; \operatorname{length}\left(p\right) \le d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_adj_iff_walk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite extended-distance bound supplies a shortest native walk. Conversely, the length of any native joining walk bounds extended distance. The distinctness condition retains looplessness.

**Theorem 1.2 (Positive powers preserve reachability).**

$$\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \left(\forall u \in V,\; \forall v \in V,\; \operatorname{Reachable}\left(\operatorname{graphPower}\left(G, d\right), u, v\right) \Leftrightarrow \operatorname{Reachable}\left(G, u, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_reachable_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Replace each power edge by its bounded base walk to obtain one direction. Every base edge remains a power edge when d is positive, giving the converse. The induced quotient equivalence identifies the actual connected components.

**Theorem 1.3 (Agreement with the existing connected supplier).**

$$\forall d \in \mathrm{Nat},\; \operatorname{Connected}\left(G\right) \Rightarrow \operatorname{graphPower}\left(G, d\right) = \operatorname{power}\left(G, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_eq_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connectedness makes every extended distance finite. Converting it to natural distance therefore preserves exactly the adjacency bound, including exponent zero.

**Theorem 1.4 (The full Minkowski sum on closed blocks).**

$$\forall n \in \mathrm{Nat},\; \operatorname{mem}\left(n, \operatorname{spectrum}\left(G\right)\right) \Leftrightarrow \left(\exists k \in \operatorname{Function}\left(iota, \mathrm{Nat}\right),\; \left(\forall i \in iota,\; \operatorname{mem}\left(\operatorname{apply}\left(k, i\right), \operatorname{spectrum}\left(\operatorname{induce}\left(G, \operatorname{fiber}\left(b, i\right)\right)\right)\right)\right) \land \operatorname{sum}\left(k\right) = n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.spectrum_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An independent dominating Finset restricts to one in every closed block. Conversely, assemble any chosen family of blockwise maximal independent Finsets. Independence and domination are both checked on the actual vertices, and the disjoint cardinality sum gives both necessity and every attainable sum.

**Theorem 1.5 (The exact disconnected well-covered-powers criterion).**

$$\left(\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \operatorname{WellCovered}\left(\operatorname{graphPower}\left(G, d\right)\right)\right) \Leftrightarrow \left(\forall C \in \operatorname{Components}\left(G\right),\; \operatorname{WCP}\left(\operatorname{componentGraph}\left(C\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.all_powers_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each exponent, well-coveredness of the union is equivalent to well-coveredness of every actual component. The forward direction varies one block set while holding the others fixed. Each component graph is connected, so its faithful power agrees with the existing connected power. No connected-only predicate is imposed on the disconnected union.

**Theorem 1.6 (Every positive power has the full component sum).**

$$\forall d \in \mathrm{Nat},\; 1 \le d \Rightarrow \left(\forall n \in \mathrm{Nat},\; \operatorname{mem}\left(n, \operatorname{spectrum}\left(\operatorname{graphPower}\left(G, d\right)\right)\right) \Leftrightarrow \left(\exists k \in \operatorname{Function}\left(\operatorname{Components}\left(G\right), \mathrm{Nat}\right),\; \left(\forall C \in \operatorname{Components}\left(G\right),\; \operatorname{mem}\left(\operatorname{apply}\left(k, C\right), \operatorname{spectrum}\left(\operatorname{power}\left(\operatorname{componentGraph}\left(C\right), d\right)\right)\right)\right) \land \operatorname{sum}\left(k\right) = n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.spectrum_power_components` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every joining walk stays in its closed component support. Inducing the base graph therefore loses no finite paths, and inducing the faithful power gives exactly the component power. Apply the full restriction-and-assembly formula to obtain both spectrum inclusions.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.all_powers_components`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_adj_iff_walk`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_eq_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.power_reachable_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.spectrum_partition`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/FiniteDistancePower.spectrum_power_components`
- Dependency: [D5/S3/Combinatorics/Graph/Products/CayleyCharacterization](../Products/CayleyCharacterization.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle](MatchingCliqueCycle.md)
- Dependency: [D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation](../ZeroForcing/GridPowerZeroForcingRefutation.md)
