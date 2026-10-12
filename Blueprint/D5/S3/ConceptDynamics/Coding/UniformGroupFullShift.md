# Uniform group endpoints and explicit full-shift coordinates

## Abstract

A uniform natural group-ring matrix has numbered-edge coordinates on the entire bilateral full shift. The inverse recovers the full expanded edge from adjacent symbols. Partition endpoints retain their coefficients and the supplied original-time chain.

**Definition 1.1 (The uniform group-ring element).**

$$\forall H \in Type,\; [\operatorname{Fintype}\left(H\right)]\operatorname{uH}\left(H\right):\operatorname{MonoidAlgebra}\left(Nat, H\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

uH is the sum of single(h,1) over every h in the finite group H. The order on H fixes the earlier chain ranks; multiplication need not commute.

**Theorem 1.2 (Every uniform coefficient is one).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall g \in H,\; \operatorname{coeff}\left(\operatorname{uH}\left(H\right), g\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uH_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every group element g, the coefficient of g in uH is exactly one.

**Definition 1.3 (The literal uniform endpoint).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, b \in Nat,\; \operatorname{uniformEndpoint}\left(n, b\right):\operatorname{GroupMat}\left(H, n, n\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uniformEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D[i,j]=b times uH for every i,j in Fin n. This is exactly b J_n u_H, with J_n the all-one matrix. The coordinate construction also covers zero dimensions or zero copy count; the source proposition uses n,b at least one.

**Theorem 1.4 (The actual copy count).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), g \in H,\; \operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{uniformEndpoint}\left(n, b\right), i, j\right), g\right) = b$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uniformEndpoint_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vertex pair and every group label has precisely b numbered parallel edges.

**Definition 1.5 (Preserve the original copy number).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), g \in H,\; \operatorname{numberEquiv}\left(n, b, i, j, g\right):\operatorname{Equiv}\left(\operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{uniformEndpoint}\left(n, b\right), i, j\right), g\right)\right), \operatorname{Fin}\left(b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.numberEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the increasing Fin cast supplied by uniformEndpoint_coeff. Its forward and inverse preserve the natural value of each original edge number.

**Definition 1.6 (The full alphabet).**

$$\forall H \in Type,\; \forall n \in Nat, b \in Nat,\; \operatorname{FullSymbol}\left(H, n, b\right) = \operatorname{Product}\left(\operatorname{Fin}\left(n\right), \operatorname{Product}\left(H, \operatorname{Fin}\left(b\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.FullSymbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A symbol is (source vertex, group coordinate, original copy number). Its cardinality is n times |H| times b.

**Definition 1.7 (All bilateral symbol sequences).**

$$\forall H \in Type,\; \forall n \in Nat, b \in Nat,\; \operatorname{FullShift}\left(H, n, b\right) = \operatorname{Function}\left(Int, \operatorname{FullSymbol}\left(H, n, b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.FullShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The domain is every function from the integers to the alphabet, with the product topology. There is no legality restriction on adjacent symbols.

**Definition 1.8 (The original positive one-step shift).**

$$\forall H \in Type,\; \forall n \in Nat, b \in Nat, x \in \operatorname{FullShift}\left(H, n, b\right), i \in Int,\; \operatorname{fullShift}\left(x, i\right) = \operatorname{x}\left(i + 1\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shift reads x(i+1) at i.

**Definition 1.9 (The left group action).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)]\forall n \in Nat, b \in Nat, h \in H, x \in \operatorname{FullShift}\left(H, n, b\right), i \in Int,\; \operatorname{fullGroupAction}\left(h, x, i\right) = \operatorname{tuple}\left(\operatorname{source}\left(\operatorname{x}\left(i\right)\right), h \cdot \operatorname{group}\left(\operatorname{x}\left(i\right)\right), \operatorname{copy}\left(\operatorname{x}\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullGroupAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Left multiplication changes only the group coordinate. Vertex and copy data remain the same.

**Definition 1.10 (Read the current expanded edge).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{uniformEndpoint}\left(n, b\right)\right)\right),\; \operatorname{fullshiftForward}\left(n, b, z\right):\operatorname{FullShift}\left(H, n, b\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftForward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every integer i, an expanded edge (source,target,label,copy,k) maps to (source,k,copy). The copy is transported by numberEquiv at those exact endpoints and label.

**Definition 1.11 (Recover the entire edge from adjacent symbols).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, x \in \operatorname{FullShift}\left(H, n, b\right),\; \operatorname{fullshiftInverse}\left(n, b, x\right):\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{uniformEndpoint}\left(n, b\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For x(i)=(s,k,c), x(i+1)=(t,kNext,cNext), return the numbered base edge (s,t,k inverse times kNext,numberEquiv inverse(c)) together with k. The seam is k times (k inverse times kNext)=kNext, with the target vertex t equal to the next source. Every full-shift sequence is admissible.

**Theorem 1.12 (Every symbol sequence is recovered).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, x \in \operatorname{FullShift}\left(H, n, b\right),\; \operatorname{fullshiftForward}\left(n, b, \operatorname{fullshiftInverse}\left(n, b, x\right)\right) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshift_inverse_forward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward map after the inverse recovers all vertices, group coordinates and copies at all integer positions.

**Theorem 1.13 (Every expanded history is recovered).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{uniformEndpoint}\left(n, b\right)\right)\right),\; \operatorname{fullshiftInverse}\left(n, b, \operatorname{fullshiftForward}\left(n, b, z\right)\right) = z$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshift_forward_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse after the forward map recovers the target by the history seam, the original label by group cancellation, and the actual dependent copy number by the increasing Fin cast roundtrip.

**Definition 1.14 (The actual full-shift homeomorphism).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat,\; [\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)]\operatorname{fullshiftHomeomorph}\left(n, b\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{uniformEndpoint}\left(n, b\right)\right)\right), \operatorname{FullShift}\left(H, n, b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For H with its discrete group topology, use the actual forward and inverse maps and the two proven identities. Forward continuity follows from the current coordinate; inverse continuity from i and i+1. No abelian or essentiality assumption is used to construct these maps.

**Definition 1.15 (Compose the same supplied chain).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right),\; \operatorname{chainFullshiftHomeomorph}\left(c\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), \operatorname{FullShift}\left(H, m, b\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose chainHistoryHomeomorph(c) with fullshiftHomeomorph(m,b), in that order. The chain retains every actual natural group-ring factor and its original length L. The inverse composes in reverse order.

**Definition 1.16 (Both actions and both exact window bounds).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), F \in \operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), \operatorname{FullShift}\left(H, m, b\right)\right),\; \operatorname{CoordinateLaws}\left(A, m, b, L, F\right):Prop$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.CoordinateLaws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a group H with a topology, CoordinateLaws asserts all six universal laws: F shift=shift F; F inverse shift=shift F inverse; F(hz)=hF(z); F inverse(hx)=hF inverse(x); equality of input expanded coordinates on [i,i+L] implies equality of the full output symbol at i; equality of input symbols on [i-L,i+1] implies equality of the full inverse expanded coordinate at i. All positions and both inputs are quantified. These are upper bounds, with no minimal-window claim.

**Theorem 1.17 (Recover the original dependent copy number).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, b \in Nat, i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), g \in H, i2 \in \operatorname{Fin}\left(n\right), j2 \in \operatorname{Fin}\left(n\right), g2 \in H, x \in \operatorname{Fin}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{uniformEndpoint}\left(n, b\right), i, j\right), g\right)\right),\; \operatorname{SameEndpointsAndLabel}\left(i, j, g, i2, j2, g2\right)\implies\operatorname{HEq}\left(\operatorname{numberEquivInverse}\left(n, b, i2, j2, g2, \operatorname{numberEquiv}\left(n, b, i, j, g, x\right)\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.numberEquiv_roundtrip_heq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SameEndpointsAndLabel is the conjunction i=i2,j=j2,g=g2. With these exact equality proofs, the inverse increasing Fin cast at i2,j2,g2 after the forward cast at i,j,g recovers x heterogeneously. The actual history roundtrip consumes this law when recovering its target, label and dependent copy type.

**Theorem 1.18 (The whole forward symbol at its original chain window).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), w \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), i \in Int,\; \operatorname{AgreeExpanded}\left(z, w, i, i + L\right)\implies\operatorname{value}\left(\operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), z\right), i\right) = \operatorname{value}\left(\operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), w\right), i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_forward_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AgreeExpanded means equality of the full expanded coordinates z(t)=w(t) at every integer t in [i,i+L]. It implies equality of the complete output symbol, including vertex, group coordinate and copy, at i. The endpoint forward map reads the current retained chain coordinate.

**Theorem 1.19 (The whole inverse expanded coordinate at the combined window).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right), z \in \operatorname{FullShift}\left(H, m, b\right), w \in \operatorname{FullShift}\left(H, m, b\right), i \in Int,\; \operatorname{AgreeSymbols}\left(z, w, i - L, i + 1\right)\implies\operatorname{value}\left(\operatorname{inverseApply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), z\right), i\right) = \operatorname{value}\left(\operatorname{inverseApply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), w\right), i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_inverse_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AgreeSymbols is equality at every integer in [i-L,i+1]. Adjacent symbols recover each entire endpoint edge on [i-L,i], then the actual reversed composition of the supplied ordered chain recovers its full source coordinate at i. Source, target, group label, original copy and expanded group coordinate all occur in the equality.

**Theorem 1.20 (The supplied chain preserves one-step original time).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), \operatorname{shift}\left(z\right)\right) = \operatorname{fullShift}\left(\operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every source history, the actual chain-to-full-shift composition intertwines the positive one-step shifts. L is the original supplied chain length; time is not replaced by a power.

**Theorem 1.21 (The supplied chain preserves every left group action).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right), h \in H, z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), \operatorname{groupHistory}\left(h, z\right)\right) = \operatorname{fullGroupAction}\left(h, \operatorname{apply}\left(\operatorname{chainFullshiftHomeomorph}\left(c\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every h and every source expanded history, the actual composition sends h acting on that history to h acting on its complete full-shift image. CoordinateLaws also derives the inverse time and inverse group identities from these equalities and the actual inverse homeomorphism.

**Theorem 1.22 (Both directions of the supplied-chain coordinates).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)][\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]\forall n \in Nat, m \in Nat, b \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), c \in \operatorname{Chain}\left(H, A, \operatorname{uniformEndpoint}\left(m, b\right), L\right),\; \operatorname{CoordinateLaws}\left(A, m, b, L, \operatorname{chainFullshiftHomeomorph}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_coordinate_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual homeomorphism for every supplied chain ending at b J_m u_H satisfies all six coordinate laws: original one-step time and left group action in both directions, forward [i,i+L] and inverse [i-L,i+1]. Its homeomorphism fields give both recovery identities and continuity. In the two-step C2 interpretation with m=b=2, the alphabet has eight symbols and these windows are [i,i+2] and [i-2,i+1]; applying this interpretation requires the actual literal factor identities and endpoint.

**Theorem 1.23 (Positive diagonal identity coefficients give legal edges).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), hp \in \left(\forall i \in \operatorname{Fin}\left(n\right),\; 0<\operatorname{coeff}\left(\operatorname{entry}\left(A, i, i\right), 1\right)\right),\; \operatorname{Essential}\left(\operatorname{expandedGraph}\left(A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.positive_essential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At each expanded vertex (i,k), an identity-labelled diagonal edge with copy zero supplies both an outgoing edge and an incoming edge. The assumption is on every diagonal identity coefficient; no global positivity or nonzero dimension is needed.

**Definition 1.24 (The literal Jordan superdiagonal predicate).**

$$\forall parts \in \operatorname{List}\left(Nat\right), i \in Nat, j \in Nat,\; \operatorname{jordanActive}\left(parts, i, j\right):Bool$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.jordanActive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Process consecutive block sizes. In the current block, require j=i+1 and j below the block size; beyond it subtract that size from both indices and continue. Outside all blocks the predicate is false.

**Definition 1.25 (Independent block-diagonal Jordan entries).**

$$\forall parts \in \operatorname{List}\left(Nat\right), i \in Nat, j \in Nat,\; \operatorname{jordanBlocks}\left(parts, i, j\right):Nat$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.jordanBlocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is diag(J_part1(0),J_part2(0),...). In a diagonal block return one exactly on its upper superdiagonal; off the diagonal blocks return zero; beyond the first block subtract its size and recurse. Padding outside the total size is zero. The coefficient correspondence uses the proven identity with jordanActive.

**Definition 1.26 (Natural coefficients of the original partition endpoint).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, parts \in \operatorname{List}\left(Nat\right),\; \operatorname{partitionMatrix}\left(n, parts\right):\operatorname{GroupMat}\left(H, n, n\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let q=|H|, b=q cubed times n. An inactive Jordan entry has every coefficient b. An active entry has coefficient b+q(q-1) at the identity and b-q at each other group element. For q at least two and n at least one, all coefficients are strictly positive. For a partition of n, these entries use its actual consecutive Jordan blocks.

**Definition 1.27 (The signed source expression in the integer group ring).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)]\forall n \in Nat, parts \in \operatorname{List}\left(Nat\right),\; \operatorname{partitionSource}\left(n, parts\right):\operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \operatorname{MonoidAlgebra}\left(Int, H\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The independent literal expression is q cubed n J_n u_H + q(q times 1_H-u_H) N_parts. N_parts is the actual block-diagonal matrix jordanBlocks. Each natural coefficient of partitionMatrix casts to the coefficient of this expression; positivity is derived from q at least two and n at least one, without an additional bound hypothesis.

**Definition 1.28 (The supplied partition-chain coordinates).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, L \in Nat, parts \in \operatorname{List}\left(Nat\right), c \in \operatorname{Chain}\left(H, \operatorname{partitionMatrix}\left(n, parts\right), \operatorname{partitionMatrix}\left(n, \operatorname{replicate}\left(n, 1\right)\right), L\right),\; [\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)]\operatorname{partitionFullShift}\left(parts, c\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{partitionMatrix}\left(n, parts\right)\right)\right), \operatorname{FullShift}\left(H, n, \operatorname{card}\left(H\right)^{3} \cdot n\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionFullShift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The only chain premise is an actual supplied chain from these original endpoints. The all-one partition has zero Jordan matrix, so its endpoint is literally uniform with b=q cubed n. The homeomorphism uses this identity rather than an endpoint-equality assumption.

**Theorem 1.29 (All source partition endpoint obligations).**

$$\forall H \in Type,\; [\operatorname{Group}\left(H\right)][\operatorname{Fintype}\left(H\right)][\operatorname{LinearOrder}\left(H\right)]\forall n \in Nat, L \in Nat, parts \in \operatorname{List}\left(Nat\right), hn \in \operatorname{Positive}\left(n\right), hq \in \operatorname{AtLeast}\left(\operatorname{card}\left(H\right), 2\right), c \in \operatorname{Chain}\left(H, \operatorname{partitionMatrix}\left(n, parts\right), \operatorname{partitionMatrix}\left(n, \operatorname{replicate}\left(n, 1\right)\right), L\right),\; [\operatorname{TopologicalSpace}\left(H\right)][\operatorname{DiscreteTopology}\left(H\right)][\operatorname{IsTopologicalGroup}\left(H\right)]({\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), g \in H,\; \operatorname{IntCast}\left(\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{partitionMatrix}\left(n, parts\right), i, j\right), g\right)\right) = \operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{partitionSource}\left(n, parts\right), i, j\right), g\right)}\land {\forall i \in \operatorname{Fin}\left(n\right), j \in \operatorname{Fin}\left(n\right), g \in H,\; 0<\operatorname{coeff}\left(\operatorname{entry}\left(\operatorname{partitionMatrix}\left(n, parts\right), i, j\right), g\right)}\land {\operatorname{Essential}\left(\operatorname{expandedGraph}\left(\operatorname{partitionMatrix}\left(n, parts\right)\right)\right)})\land\operatorname{card}\left(\operatorname{FullSymbol}\left(H, n, \operatorname{card}\left(H\right)^{3} \cdot n\right)\right) = \operatorname{card}\left(H\right)^{4} \cdot n^{2}\land\operatorname{CoordinateLaws}\left(\operatorname{partitionMatrix}\left(n, parts\right), n, \operatorname{card}\left(H\right)^{3} \cdot n, L, \operatorname{partitionFullShift}\left(parts, c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partition_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed coefficient cast, positivity and essentiality clauses quantify every original i,j,g. IntCast is the ordinary natural-to-integer coefficient map. The same theorem proves alphabet q to the fourth times n squared and all six CoordinateLaws for the supplied chain. Taking L=largestPart-1 gives forward [i,i+largestPart-1] and inverse [i-(largestPart-1),i+1]. This does not prove chain existence or a minimal window.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.CoordinateLaws`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.FullShift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.FullSymbol`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_coordinate_laws`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_forward_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_group`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_homeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_inverse_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.chain_fullshift_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullGroupAction`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullShift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftForward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshiftInverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshift_forward_inverse`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.fullshift_inverse_forward`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.jordanActive`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.jordanBlocks`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.numberEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.numberEquiv_roundtrip_heq`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionFullShift`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionMatrix`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partitionSource`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.partition_coordinates`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.positive_essential`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uH`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uH_coeff`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uniformEndpoint`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/UniformGroupFullShift.uniformEndpoint_coeff`
- Dependency: [D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories](OrderedGroupChainHistories.md)
