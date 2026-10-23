# Splicing the Complete Native T Core

## Abstract

Actual native circle complements and literal c edges construct a Hamilton cycle on the complete two-star T core union.

**Theorem 1.1 (The Core Swap Followed by bc Is One Rotation).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \mathrm{mul}\left(\mathrm{swap}\left(0, m\right), \mathrm{mul}\left(\mathrm{b}\left(m\right), \mathrm{c}\left(m\right)\right)\right) = \mathrm{finRotate}\left(\mathrm{add}\left(m, 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.tau_bc_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the literal swap of zero and the final position, followed by b*c, is finRotate(m+1). This coordinate identity is consumed by the actual J2 surviving-row proof.

**Definition 1.2 (The Actual T Cut Start).**

$$\forall m \in \mathrm{Nat},\; \left(\forall i \in \mathrm{Fin}\left(m\right),\; \mathrm{cutStart}\left(\mathrm{inl}\left(i\right)\right) = \mathrm{ite}\left(\mathrm{val}\left(i\right) = \mathrm{sub}\left(m, 1\right), 1, \mathrm{tCircleAnchor}\left(\mathrm{inl}\left(i\right)\right)\right)\right) \land \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{cutStart}\left(\mathrm{inr}\left(j\right)\right) = \mathrm{tCircleAnchor}\left(\mathrm{inr}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.cutStart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The T cut starts at its owner port, except that the identity core starts literally at the identity.

**Definition 1.3 (The Actual T Cut Generator).**

$$\forall m \in \mathrm{Nat},\; \left(\forall i \in \mathrm{Fin}\left(m\right),\; \mathrm{cutGenerator}\left(\mathrm{inl}\left(i\right)\right) = \mathrm{ite}\left(\mathrm{sub}\left(m, 2\right) \le \mathrm{val}\left(i\right), \mathrm{a}\left(m\right), \mathrm{b}\left(m\right)\right)\right) \land \left(\forall j \in \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right),\; \mathrm{cutGenerator}\left(\mathrm{inr}\left(j\right)\right) = \mathrm{b}\left(m\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.cutGenerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two core cuts use a; each noncore cut uses b.

**Theorem 1.4 (T Cut Starts Have Their Declared Circle Owners).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\forall p \in \mathrm{Sum}\left(\mathrm{Fin}\left(m\right), \mathrm{Fin}\left(\mathrm{sub}\left(m, 2\right)\right)\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{Circle}\left(\mathrm{cutStart}\left(p\right), v\right) \Leftrightarrow \mathrm{Circle}\left(\mathrm{tCircleAnchor}\left(p\right), v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_cut_circle_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For m at least four, the actual cut start and the independently indexed T anchor define the same complete circle domain.

For m at least four, configurations are the actual permutations of Fin(m+1). The generators a, b and c reverse the first m+1, m and m-1 positions. Let tau exchange position zero with the last position. CoreDomain(m) is the union of the two insertion stars supplied by a*c and tau*a*c. Each star is specified by deleting its last label from the actual oriented tuple circle, allowing whole reversal. The graph coreGraph(m) is the full three-generator Cayley graph induced on this independently specified union. CoreDeletedEdge(m) is the literal set of old T cuts: one a edge at each core and one b edge at each noncore port. It is specified from those actual ports before any paths or cycle are chosen. CoreUncut(m,e) holds when an actual T owner contributes the native circle edge e and e differs from that owner's cut. TSeam(m,e) holds when e joins an owner's cut endpoint to that endpoint times c. Both predicates are independent of the constructed cycle. configurationEdges(w) means w.edges mapped through the underlying-configuration projection.

**Theorem 1.5 (One Actual Core Hamilton Cycle with Its Complete Edge Set).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists z \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(z\right) = 1 \land \left(\exists w \in \mathrm{Walk}\left(\mathrm{coreGraph}\left(m\right), z, z\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\exists y \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(y\right) = \mathrm{c}\left(m\right) \land \mathrm{headOption}\left(\mathrm{edges}\left(w\right)\right) = \mathrm{some}\left(\mathrm{Sym2}\left(z, y\right)\right)\right) \land \left(\left(\forall x \in \mathrm{CoreVertices}\left(m\right),\; \forall y \in \mathrm{CoreVertices}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land \left(\mathrm{val}\left(y\right) = \mathrm{rightMultiply}\left(\mathrm{val}\left(x\right), g\right) \land \left(\neg \mathrm{CoreDeletedEdge}\left(m, \mathrm{Sym2}\left(\mathrm{val}\left(x\right), \mathrm{val}\left(y\right)\right)\right)\right)\right)\right) \Rightarrow \mathrm{mem}\left(\mathrm{Sym2}\left(x, y\right), \mathrm{edges}\left(w\right)\right)\right) \land \left(\forall e \in \mathrm{Sym2Type}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{mem}\left(e, \mathrm{configurationEdges}\left(w\right)\right) \Leftrightarrow \left(\mathrm{CoreUncut}\left(m, e\right) \lor \mathrm{TSeam}\left(m, e\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle_with_full_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a core vertex z whose actual configuration is the identity and a genuine coreGraph(m) Hamilton cycle w based at z. Every core vertex occurs exactly once before the return. The first edge of w joins z to a vertex whose configuration is exactly c(m), so the closing connection is a literal generator edge, rather than an endpoint pairing assumption. Every native a or b edge between core vertices is retained in the actual cycle whenever its underlying configuration edge is outside CoreDeletedEdge(m). Moreover, for every arbitrary undirected configuration edge e, membership in configurationEdges(w) is equivalent to CoreUncut(m,e) or TSeam(m,e). This characterizes the complete edge set on the same actual cycle.

The earned circle partition has Fin(m) plus Fin(m-2) owners. In T order, take the identity core, all lower noncore gaps, the tau core and all upper noncore gaps. At the two cores use the actual a-edge complements; at every other circle use the actual b-edge complement. Each complement is a path of length 2(m+1)-1 that exhausts its complete independent circle domain. Lift these paths to the induced graph. Unique ownership makes their full supports disjoint, and full ownership makes every core vertex occur once.

The noncore seam identity is a*c*(b*c)^j*b*c = a*c*(b*c)^(j+1). The native halfword identity a*c*(b*c)^(m-2)=tau connects the lower half to the second a complement and makes the upper half return to identity. The complete cut list is therefore a closed chain of actual c connections. PathRingSplicing joins the full paths and returns their closing edge first; multiplying the final seam by the involution c identifies its endpoint as c. The complete native-complement edge inventory earns every other a/b edge in its owned circle. The induced-walk edge map and injective subtype map preserve that membership. Each piece edge occurs in the literal chainEdges list and therefore in the final reversed cycle edge list. This proves the retained-edge assertion on the same actual Hamilton cycle. Exact native complement equivalences characterize all raw piece edges. The exhaustive chain_edge_cases theorem classifies every chain edge as a piece edge or a consecutive c seam. The actual last piece owns the closing c seam. Conversely, every owner occurs in the literal cut list, so all its uncut piece edges and its actual c seam occur in this same cycle.

**Theorem 1.6 (The Established Core Cycle and Retention API).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists z \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(z\right) = 1 \land \left(\exists w \in \mathrm{Walk}\left(\mathrm{coreGraph}\left(m\right), z, z\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\exists y \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(y\right) = \mathrm{c}\left(m\right) \land \mathrm{headOption}\left(\mathrm{edges}\left(w\right)\right) = \mathrm{some}\left(\mathrm{Sym2}\left(z, y\right)\right)\right) \land \left(\forall x \in \mathrm{CoreVertices}\left(m\right),\; \forall y \in \mathrm{CoreVertices}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land \left(\mathrm{val}\left(y\right) = \mathrm{rightMultiply}\left(\mathrm{val}\left(x\right), g\right) \land \left(\neg \mathrm{CoreDeletedEdge}\left(m, \mathrm{Sym2}\left(\mathrm{val}\left(x\right), \mathrm{val}\left(y\right)\right)\right)\right)\right)\right) \Rightarrow \mathrm{mem}\left(\mathrm{Sym2}\left(x, y\right), \mathrm{edges}\left(w\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original core Hamilton cycle API remains available with its complete support, actual first c edge and retained native edges. It uses the same construction above and projects these existing conclusions. Contact iteration consumers retain their original witness structure.

This theorem constructs the entire initial two-star core for every m at least four. It does not yet cover the remaining insertion stars of the full second layer, prove their complete actual contact classification, or establish the higher simultaneous boundary induction. Those are separate remaining obligations for all-size three-prefix-reversal Hamiltonicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.cutGenerator`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.cutStart`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle_with_full_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_cut_circle_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.tau_bc_rotation`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership](NativeCircleOwnership.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches](NativeSwitches.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](../Walks/PathRingSplicing.md)
