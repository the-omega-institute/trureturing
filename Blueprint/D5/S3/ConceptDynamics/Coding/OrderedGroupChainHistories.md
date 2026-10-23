# Ordered group chain histories

## Abstract

Signed anchors identify every expanded history with a numbered base path and one group coordinate. Ordered overlap steps compose at the original time with exact asymmetric windows.

An edge retains its source, target, group label and copy number. All finite matrix dimensions, zero coefficient fibers and zero chain lengths are allowed. The finite group order fixes each local increasing rank. The sufficient local identities do not require an inhabited vertex set or an essentiality premise.

An indexed chain has d(j) for j in Fin(L+1), square matrices A(j) at dimension d(j), and rectangular U(j), V(j) for j in Fin(L), with A(j)=U(j)V(j) and A(j+1)=V(j)U(j). Its recursive Chain is toChain of that same indexed data; the endpoint matrices are A(0) and A(L). Thus every chain formula below applies to these actual supplied factors, including essential chains.

**Definition 1.1 (Increasing positive labels).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \forall x \in \operatorname{Path}\left(A\right), t \in Nat,\; \operatorname{positiveLabels}\left(x, t + 1\right) = \operatorname{Append}\left(\operatorname{positiveLabels}\left(x, t\right), \operatorname{Singleton}\left(\operatorname{label}\left(\operatorname{edgeAt}\left(x, \operatorname{IntOfNat}\left(t\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.positiveLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero list is empty. Appending the current label preserves the temporal order.

**Definition 1.2 (Descending inverse labels).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \forall x \in \operatorname{Path}\left(A\right), t \in Nat,\; \operatorname{negativeLabels}\left(x, t + 1\right) = \operatorname{Append}\left(\operatorname{negativeLabels}\left(x, t\right), \operatorname{Singleton}\left(\operatorname{label}\left(\operatorname{edgeAt}\left(x, -\operatorname{IntOfNat}\left(t + 1\right)\right)\right)^{-1}\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.negativeLabels` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero the list is empty. Its successive entries are a(-1) inverse, a(-2) inverse and so on, in descending time order.

**Definition 1.3 (All signed coordinates from one anchor).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \forall x \in \operatorname{Path}\left(A\right), k \in H, t \in Int,\; \operatorname{anchoredCoordinate}\left(x, k, t\right):H$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchoredCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every integer is either Int.ofNat(s) or Int.negSucc(s), for s:Nat. The first coordinate is k times ListProd(positiveLabels(x,s)); the second is k times ListProd(negativeLabels(x,s+1)). Positive labels keep increasing time order, negative inverse labels keep descending time order, and the coordinate at zero is k.

**Theorem 1.4 (The signed one-step recurrence).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), x \in \operatorname{Path}\left(A\right), k \in H, t \in Int,\; \operatorname{anchoredCoordinate}\left(x, k, t\right) \cdot \operatorname{label}\left(\operatorname{edgeAt}\left(x, t\right)\right) = \operatorname{anchoredCoordinate}\left(x, k, t + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_seam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recurrence holds at every integer, including the seam from minus one to zero.

**Theorem 1.5 (Uniqueness on both signed tails).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), x \in \operatorname{Path}\left(A\right), k \in H, g \in Int \to H,\; ((((\operatorname{g}\left(0\right) = k) \land (\forall t \in Int,\; \operatorname{g}\left(t\right) \cdot \operatorname{label}\left(\operatorname{edgeAt}\left(x, t\right)\right) = \operatorname{g}\left(t + 1\right)))) \implies (\forall t \in Int,\; \operatorname{g}\left(t\right) = \operatorname{anchoredCoordinate}\left(x, k, t\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Forward induction and inverse recurrence induction recover all coordinates. There is no period constraint.

**Definition 1.6 (Unrestricted anchored homeomorphism).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), continuousGroup \in \operatorname{IsTopologicalGroup}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right),\; \operatorname{anchoredHomeomorph}\left(A\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), \operatorname{Prod}\left(\operatorname{Path}\left(A\right), H\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchoredHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map keeps the numbered base path and the group coordinate at zero. The inverse reconstructs both signed tails. Each coordinate uses finitely many input labels, giving continuity in the product topology.

**Theorem 1.7 (The positive original-time action).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), continuousGroup \in \operatorname{IsTopologicalGroup}\left(H\right),\; \forall n \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{anchoredHomeomorph}\left(A\right), \operatorname{historyShift}\left(\operatorname{expandedGraph}\left(A\right), z\right)\right) = \operatorname{step}\left(A, \operatorname{apply}\left(\operatorname{anchoredHomeomorph}\left(A\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The base path shifts by one and the anchor multiplies on the right by the current edge label.

**Theorem 1.8 (All forward seams).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{Seam}\left(\operatorname{countedExpansion}\left(U \cdot V\right), \operatorname{countedExpansion}\left(V \cdot U\right), \operatorname{orderedForward}\left(U, V\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_forward_seam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward edge joins the current V half with the next U half. Its coordinate crosses the current U half. Both output endpoints and group coordinates match.

**Theorem 1.9 (All past-aligned inverse seams).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{Seam}\left(\operatorname{countedExpansion}\left(V \cdot U\right), \operatorname{countedExpansion}\left(U \cdot V\right), \operatorname{orderedBackward}\left(U, V\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_backward_seam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse reads U from the preceding output, V from the central output, and uses the central group coordinate multiplied by the inverse U label.

**Theorem 1.10 (Both center recoveries).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{LocalCriterion}\left(\operatorname{orderedOverlapInput}\left(U, V\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_local_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two seams and both center recoveries hold on every actual three-edge word. The same ordered ranks recover all parallel-edge numbers.

**Definition 1.11 (The actual ordered overlap homeomorphism).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, U \in \operatorname{GroupMat}\left(H, n, m\right), V \in \operatorname{GroupMat}\left(H, m, n\right),\; \operatorname{orderedHistoryHomeomorph}\left(U, V\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(U \cdot V\right)\right), \operatorname{History}\left(\operatorname{expandedGraph}\left(V \cdot U\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.orderedHistoryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Applying the two tables at radii (0,1) and (1,0) gives continuous inverse maps on all legal histories, including empty carriers.

**Definition 1.12 (The actual ordered layer transfers).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), x \in \operatorname{Path}\left(A\right),\; \operatorname{chainTransfers}\left(c, x\right):\operatorname{List}\left(H\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainTransfers` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a cons layer, first record the U label at position zero, then evaluate the remaining transfer list at the actual output path of that layer. A nil chain gives the empty list.

**Definition 1.13 (Gamma as the ordered list product).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), x \in \operatorname{Path}\left(A\right),\; \operatorname{chainGamma}\left(c, x\right) = \operatorname{ListProd}\left(\operatorname{chainTransfers}\left(c, x\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is c0(x0) c1(x1) through the last layer in precisely this order. At length zero it is one.

**Definition 1.14 (Expanded ordered-chain homeomorphism).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{chainHistoryHomeomorph}\left(c\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), \operatorname{History}\left(\operatorname{expandedGraph}\left(B\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainHistoryHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose each original forward table in increasing layer order. The inverse composes the original past-aligned inverse tables in decreasing layer order. No swapped forward algorithm is substituted.

**Definition 1.15 (The same base-path homeomorphism).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{chainBaseHomeomorph}\left(c\right):\operatorname{Homeomorph}\left(\operatorname{Path}\left(A\right), \operatorname{Path}\left(B\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainBaseHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base maps are obtained from the same prescribed overlap algorithms. Both directions are continuous.

**Theorem 1.16 (Forward formula for the whole actual chain).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), p \in \operatorname{Prod}\left(\operatorname{Path}\left(A\right), H\right),\; \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), p\right) = (\operatorname{apply}\left(\operatorname{chainBaseEquiv}\left(c\right), \operatorname{first}\left(p\right)\right),\operatorname{second}\left(p\right) \cdot \operatorname{chainGamma}\left(c, \operatorname{first}\left(p\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_forward_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each successive right multiplication follows the retained transfer list. Both composites are identities because each original step is inverted.

**Theorem 1.17 (Inverse formula with the same Gamma).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), p \in \operatorname{Prod}\left(\operatorname{Path}\left(B\right), H\right),\; \operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainSkewHomeomorph}\left(c\right)\right), p\right) = (\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainBaseEquiv}\left(c\right)\right), \operatorname{first}\left(p\right)\right),\operatorname{second}\left(p\right) \cdot \operatorname{chainGamma}\left(c, \operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainBaseEquiv}\left(c\right)\right), \operatorname{first}\left(p\right)\right)\right)^{-1})$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_inverse_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse of the product reverses the factor order. Gamma is evaluated at the recovered base history.

**Theorem 1.18 (Expanded and product algorithms agree).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{anchoredHomeomorph}\left(B\right), \operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), z\right)\right) = \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), \operatorname{apply}\left(\operatorname{anchoredHomeomorph}\left(A\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_anchored_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This identifies the two actual implementations on every signed history.

**Theorem 1.19 (Exact noncommutative telescoping).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), x \in \operatorname{Path}\left(A\right),\; \operatorname{label}\left(\operatorname{edgeAt}\left(x, 0\right)\right) \cdot \operatorname{chainGamma}\left(c, \operatorname{shift}\left(A, x\right)\right) = \operatorname{chainGamma}\left(c, x\right) \cdot \operatorname{label}\left(\operatorname{edgeAt}\left(\operatorname{apply}\left(\operatorname{chainBaseHomeomorph}\left(c\right), x\right), 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local label equations cancel only adjacent intermediate labels. No commutativity, positivity or periodicity is used.

**Theorem 1.20 (Continuity of Gamma).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right),\; \operatorname{Continuous}\left(\operatorname{chainGamma}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_gamma_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered transfer function is continuous, as the group coordinate of the same continuous skew map at anchor one.

**Theorem 1.21 (Whole-chain original-time transport).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), p \in \operatorname{Prod}\left(\operatorname{Path}\left(A\right), H\right),\; \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), \operatorname{step}\left(A, p\right)\right) = \operatorname{step}\left(B, \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All layers commute with the positive single time step, so their composition does too.

**Theorem 1.22 (Whole-chain left equivariance).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), h \in H, p \in \operatorname{Prod}\left(\operatorname{Path}\left(A\right), H\right),\; \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), \operatorname{translate}\left(h, p\right)\right) = \operatorname{translate}\left(h, \operatorname{apply}\left(\operatorname{chainSkewHomeomorph}\left(c\right), p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left multiplication commutes with the ordered right transfer.

**Theorem 1.23 (Expanded original-time transport).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), \operatorname{historyShift}\left(\operatorname{expandedGraph}\left(A\right), z\right)\right) = \operatorname{historyShift}\left(\operatorname{expandedGraph}\left(B\right), \operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_history_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The expanded map commutes with the same positive single-step shift.

**Theorem 1.24 (Both expanded left-action laws).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), h \in H,\; ((\forall z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right),\; \operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), \operatorname{groupHistory}\left(A, h, z\right)\right) = \operatorname{groupHistory}\left(B, h, \operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), z\right)\right)) \land (\forall w \in \operatorname{History}\left(\operatorname{expandedGraph}\left(B\right)\right),\; \operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainHistoryHomeomorph}\left(c\right)\right), \operatorname{groupHistory}\left(B, h, w\right)\right) = \operatorname{groupHistory}\left(A, h, \operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainHistoryHomeomorph}\left(c\right)\right), w\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_history_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both the forward map and its reverse-layer inverse preserve the left group action.

**Theorem 1.25 (Forward expanded window).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), w \in \operatorname{History}\left(\operatorname{expandedGraph}\left(A\right)\right), i \in Int,\; ((\forall t \in Int,\; ((((i \leq t) \land (t \leq i + \operatorname{IntOfNat}\left(L\right)))) \implies (\operatorname{edgeAt}\left(z, t\right) = \operatorname{edgeAt}\left(w, t\right)))) \implies (\operatorname{edgeAt}\left(\operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), z\right), i\right) = \operatorname{edgeAt}\left(\operatorname{apply}\left(\operatorname{chainHistoryHomeomorph}\left(c\right), w\right), i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_forward_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct forward-algorithm induction gives [i,i+L] for every integer i.

**Theorem 1.26 (Inverse expanded window).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right), topology \in \operatorname{TopologicalSpace}\left(H\right), discrete \in \operatorname{DiscreteTopology}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), z \in \operatorname{History}\left(\operatorname{expandedGraph}\left(B\right)\right), w \in \operatorname{History}\left(\operatorname{expandedGraph}\left(B\right)\right), i \in Int,\; ((\forall t \in Int,\; ((((i - \operatorname{IntOfNat}\left(L\right) \leq t) \land (t \leq i))) \implies (\operatorname{edgeAt}\left(z, t\right) = \operatorname{edgeAt}\left(w, t\right)))) \implies (\operatorname{edgeAt}\left(\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainHistoryHomeomorph}\left(c\right)\right), z\right), i\right) = \operatorname{edgeAt}\left(\operatorname{apply}\left(\operatorname{symm}\left(\operatorname{chainHistoryHomeomorph}\left(c\right)\right), w\right), i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_inverse_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct inverse-algorithm induction gives [i-L,i], with decreasing layer order.

**Theorem 1.27 (Exact initial window of Gamma).**

$$\forall H \in Type, group \in \operatorname{Group}\left(H\right), finite \in \operatorname{Fintype}\left(H\right), order \in \operatorname{LinearOrder}\left(H\right),\; \forall n \in Nat, m \in Nat, L \in Nat, A \in \operatorname{GroupMat}\left(H, n, n\right), B \in \operatorname{GroupMat}\left(H, m, m\right), c \in \operatorname{Chain}\left(H, A, B, L\right), x \in \operatorname{Path}\left(A\right), y \in \operatorname{Path}\left(A\right),\; ((\forall t \in Int,\; ((((0 \leq t) \land (t \leq \operatorname{IntOfNat}\left(L\right) - 1))) \implies (\operatorname{edgeAt}\left(x, t\right) = \operatorname{edgeAt}\left(y, t\right)))) \implies (\operatorname{chainGamma}\left(c, x\right) = \operatorname{chainGamma}\left(c, y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_gamma_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first transfer reads position zero. Transfer j reads only [0,j], so the union is [0,L-1]. At L=0 the interval is empty, the history map is the identity and Gamma is one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchoredCoordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchoredHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_seam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.anchored_unique`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainBaseHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainGamma`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainHistoryHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chainTransfers`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_anchored_formula`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_cocycle`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_forward_formula`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_forward_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_gamma_continuous`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_gamma_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_group`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_history_group`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_history_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_inverse_formula`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_inverse_window`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.chain_time`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.negativeLabels`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.orderedHistoryHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_backward_seam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_forward_seam`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.ordered_local_criterion`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OrderedGroupChainHistories.positiveLabels`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedGroupChainPaths](CountedGroupChainPaths.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FiniteWindowTableCriterion](FiniteWindowTableCriterion.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/FixedBlockRigidity](FixedBlockRigidity.md)
