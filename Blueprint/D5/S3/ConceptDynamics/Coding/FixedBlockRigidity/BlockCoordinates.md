# Coordinates for actual fixed blocks

## Abstract

Exact integer, block and actual-edge coordinates support the constructed fixed-block code.

History(G) is the actual legal bilateral edge history. translate(G,a,x) has edge x(i+a) at every integer i. For positive k, blockAddress(hk,i) is the Euclidean quotient i/k together with the finite remainder (i mod k).toNat, and assemble(k,(j,r)) is j*k+r.val in the integers. NatPositive(k) means 0<k. These coordinates include negative positions and the case k=1.

**Theorem 1.1 (Unit time determines every integer translation).**

$$\forall V \in Type, E \in Type, D \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), F \in \operatorname{DirectedMultigraph}\left(V, D\right), h \in {\operatorname{History}\left(G\right)\to \operatorname{History}\left(F\right)}, step \in \left(\forall x \in \operatorname{History}\left(G\right),\; \operatorname{apply}\left(h, \operatorname{shift}\left(G, x\right)\right) = \operatorname{shift}\left(F, \operatorname{apply}\left(h, x\right)\right)\right),\; \forall offset \in Int, x \in \operatorname{History}\left(G\right),\; \operatorname{apply}\left(h, \operatorname{translate}\left(G, offset, x\right)\right) = \operatorname{translate}\left(F, offset, \operatorname{apply}\left(h, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.translate_commutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two directed multigraphs on the same vertex type and an arbitrary map between their actual history spaces, commutation with one forward shift implies commutation with every integer translation. No continuity, invertibility, finiteness or essentiality of the history map is assumed. This supplier is consumed by center_depends_only_on_edge, extract_edge_map and rigidity_of_fixed_block_law.

**Theorem 1.2 (Reassemble every integer position).**

$$\forall k \in Nat, hk \in \operatorname{NatPositive}\left(k\right), i \in Int,\; \operatorname{assemble}\left(k, \operatorname{blockAddress}\left(hk, i\right)\right) = i$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.assemble_address` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact quotient and nonnegative finite remainder reassemble the original integer, including negative positions. The parent construction uses this equation for block seams, the inverse map, the operational output, group action and block-time translation.

**Theorem 1.3 (Recover the exact block and offset).**

$$\forall k \in Nat, hk \in \operatorname{NatPositive}\left(k\right), pair \in \operatorname{Product}\left(Int, \operatorname{Fin}\left(k\right)\right),\; \operatorname{blockAddress}\left(hk, \operatorname{assemble}\left(k, pair\right)\right) = pair$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.address_assemble` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer block index and every offset in Fin(k) is recovered after assembly. The proof uses injectivity of the original assembly map and assemble_address. blockOutput_at consumes this precise pair identity.

**Theorem 1.4 (Natural iterates are the same translation).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), m \in Nat, x \in \operatorname{History}\left(G\right),\; \operatorname{iterateApply}\left(\operatorname{shift}\left(G\right), m, x\right) = \operatorname{translate}\left(G, \operatorname{intOfNat}\left(m\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.shift_iterate_translate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

iterateApply(f,m,x) means Function.iterate f m applied to x, and intOfNat is the natural-to-integer coercion. The statement covers m=0 and every actual legal history. constructed_k_shift uses it in both graph spaces to turn the established k-translation equation into the k-step law.

**Theorem 1.5 (Keep every actual parallel edge).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finiteH \in \operatorname{Fintype}\left(H\right), n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), first \in \operatorname{Edge}\left(A\right), second \in \operatorname{Edge}\left(A\right), sameSource \in \operatorname{source}\left(first\right) = \operatorname{source}\left(second\right), sameTarget \in \operatorname{target}\left(first\right) = \operatorname{target}\left(second\right), sameLabel \in \operatorname{label}\left(first\right) = \operatorname{label}\left(second\right), sameNumber \in \operatorname{numberValue}\left(first\right) = \operatorname{numberValue}\left(second\right),\; first = second$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.edge_eq_of_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An Edge(A) retains its source, target, group label and finite parallel-edge number. Equal values of all four coordinates imply equality of the actual edges, including the dependent Fin proof component. prefixLastCoordinates consumes this statement in its inverse construction; equality of labels or endpoints alone is insufficient.

The original splice construction keeps the past of one legal history and the future of another when their actual edges at zero agree. The original finite-context edge realization supplies a history containing each actual edge at zero. The counted-edge coordinate equivalence supplies the same Fintype instance used by the parent. These original suppliers are relocated directly and have retained consumers; they introduce no wrapper theorem or added mathematical assumption. Their reduced live dependencies and each module's admission remain separate current-check obligations.

The terminal original18.3 edge-rigidity, free-expansion equality and equal-power attachment statements remain in FixedBlockRigidity with the original Scribe formulas. The accepted attachment still assumes the explicit natural equality A^k=B^k. This coordinate module does not derive original dimension-group inertness, least positive tau or the rational n*b_H cutoff, and does not exclude overlapping block codes or other original-time conjugacies.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.address_assemble`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.assemble_address`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.edge_eq_of_coordinates`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.shift_iterate_translate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/FixedBlockRigidity/BlockCoordinates.translate_commutation`
- Dependency: [D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy](../BipartiteOverlapConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupOverlap](../CountedGroupOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding](../EquivariantOverlapRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion](../FiniteWindowTableCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](../RectangularNilpotenceBarrier.md)
