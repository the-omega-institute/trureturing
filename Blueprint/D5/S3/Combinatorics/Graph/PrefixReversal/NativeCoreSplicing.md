# Splicing the Complete Native T Core

## Abstract

Actual native circle complements and literal c edges construct a Hamilton cycle on the complete two-star T core union.

For m at least four, configurations are the actual permutations of Fin(m+1). The generators a, b and c reverse the first m+1, m and m-1 positions. Let tau exchange position zero with the last position. CoreDomain(m) is the union of the two insertion stars supplied by a*c and tau*a*c. Each star is specified by deleting its last label from the actual oriented tuple circle, allowing whole reversal. The graph coreGraph(m) is the full three-generator Cayley graph induced on this independently specified union. CoreDeletedEdge(m) is the literal set of old T cuts: one a edge at each core and one b edge at each noncore port. It is specified from those actual ports before any paths or cycle are chosen.

**Theorem 1.1 (One Actual Hamilton Cycle Covers the Whole Core Union).**

$$\forall m \in \mathrm{Nat},\; 4 \le m \Rightarrow \left(\exists z \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(z\right) = 1 \land \left(\exists w \in \mathrm{Walk}\left(\mathrm{coreGraph}\left(m\right), z, z\right),\; \mathrm{IsHamiltonianCycle}\left(w\right) \land \left(\left(\exists y \in \mathrm{CoreVertices}\left(m\right),\; \mathrm{val}\left(y\right) = \mathrm{c}\left(m\right) \land \mathrm{headOption}\left(\mathrm{edges}\left(w\right)\right) = \mathrm{some}\left(\mathrm{Sym2}\left(z, y\right)\right)\right) \land \left(\forall x \in \mathrm{CoreVertices}\left(m\right),\; \forall y \in \mathrm{CoreVertices}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land \left(\mathrm{val}\left(y\right) = \mathrm{rightMultiply}\left(\mathrm{val}\left(x\right), g\right) \land \left(\neg \mathrm{CoreDeletedEdge}\left(m, \mathrm{Sym2}\left(\mathrm{val}\left(x\right), \mathrm{val}\left(y\right)\right)\right)\right)\right)\right) \Rightarrow \mathrm{mem}\left(\mathrm{Sym2}\left(x, y\right), \mathrm{edges}\left(w\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is a core vertex z whose actual configuration is the identity and a genuine coreGraph(m) Hamilton cycle w based at z. Every core vertex occurs exactly once before the return. The first edge of w joins z to a vertex whose configuration is exactly c(m), so the closing connection is a literal generator edge, rather than an endpoint pairing assumption. Every native a or b edge between core vertices is retained in the actual cycle whenever its underlying configuration edge is outside CoreDeletedEdge(m).

The earned circle partition has Fin(m) plus Fin(m-2) owners. In T order, take the identity core, all lower noncore gaps, the tau core and all upper noncore gaps. At the two cores use the actual a-edge complements; at every other circle use the actual b-edge complement. Each complement is a path of length 2(m+1)-1 that exhausts its complete independent circle domain. Lift these paths to the induced graph. Unique ownership makes their full supports disjoint, and full ownership makes every core vertex occur once.

The noncore seam identity is a*c*(b*c)^j*b*c = a*c*(b*c)^(j+1). The native halfword identity a*c*(b*c)^(m-2)=tau connects the lower half to the second a complement and makes the upper half return to identity. The complete cut list is therefore a closed chain of actual c connections. PathRingSplicing joins the full paths and returns their closing edge first; multiplying the final seam by the involution c identifies its endpoint as c. The complete native-complement edge inventory earns every other a/b edge in its owned circle. The induced-walk edge map and injective subtype map preserve that membership. Each piece edge occurs in the literal chainEdges list and therefore in the final reversed cycle edge list. This proves the retained-edge assertion on the same actual Hamilton cycle.

This theorem constructs the entire initial two-star core for every m at least four. It does not yet cover the remaining insertion stars of the full second layer, prove their complete actual contact classification, or establish the higher simultaneous boundary induction. Those are separate remaining obligations for all-size three-prefix-reversal Hamiltonicity.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCoreSplicing.native_core_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleOwnership](NativeCircleOwnership.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches](NativeSwitches.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PathRingSplicing](../Walks/PathRingSplicing.md)
