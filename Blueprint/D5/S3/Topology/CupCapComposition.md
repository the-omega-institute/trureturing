# Generator paths and internal components

## Abstract

Generator paths and internal components

Top ports are (false,j) and (false,j+1), written A and B. A generator retains their exterior cup and reconnects the partners of the sewn inputs. Explicit paths in the actual half-edge gluing prove the formula, without imposing a representation or replacing the algebra. When the inputs are paired, their four glued half-edges form a component with no outer endpoint; otherwise every half-edge has an explicit path to the outer boundary.

**Definition 1.1 (reconnected).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\forall x \in \operatorname{Boundary}\left(n\right),\; \operatorname{reconnected}\left(j, d, x\right) = \operatorname{If}\left(x = \operatorname{Pair}\left(False, j\right), \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right), \operatorname{If}\left(x = \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right), \operatorname{Pair}\left(False, j\right), \operatorname{If}\left(\operatorname{mate}\left(d, x\right) = \operatorname{Pair}\left(False, j\right), \operatorname{mate}\left(d, \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right)\right), \operatorname{If}\left(\operatorname{mate}\left(d, x\right) = \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right), \operatorname{mate}\left(d, \operatorname{Pair}\left(False, j\right)\right), \operatorname{mate}\left(d, x\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/CupCapComposition.reconnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two generator outputs are paired directly. All other outputs follow the old matching, except for reconnecting the two old partners.

**Theorem 1.2 (composite_cupcap_mate).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\forall x \in \operatorname{Boundary}\left(n\right),\; \operatorname{mate}\left(\operatorname{composite}\left(\operatorname{cupcapMatching}\left(j\right), d\right), x\right) = \operatorname{reconnected}\left(j, d, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.composite_cupcap_mate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reconstructed partner is distinct from the starting endpoint and lies in its glued component. Completeness of the actual endpoint pairing identifies it with composite.

**Theorem 1.3 (internalLoopCount_cupcap_zero).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\operatorname{Not}\left(\operatorname{mate}\left(d, \operatorname{Pair}\left(False, j\right)\right) = \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right)\right) \Rightarrow \operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j\right), d\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every tagged half-edge reaches an exposed endpoint, so the internal-component subtype is empty.

**Theorem 1.4 (internalLoopCount_cupcap_pos).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\operatorname{mate}\left(d, \operatorname{Pair}\left(False, j\right)\right) = \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right) \Rightarrow \operatorname{Positive}\left(\operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j\right), d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The paired input component is isolated by a component-invariant patch coloring, providing an element of the finite internal-component subtype.

**Theorem 1.5 (internalLoopCount_cupcap_eq_zero_iff).**

$$\forall n \in Nat,\; \forall j \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right),\; \operatorname{Less}\left(\operatorname{Add}\left(j, 1\right), n\right) \Rightarrow \left(\operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j\right), d\right) = 0 \Leftrightarrow \operatorname{Not}\left(\operatorname{mate}\left(d, \operatorname{Pair}\left(False, j\right)\right) = \operatorname{Pair}\left(False, \operatorname{Add}\left(j, 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two directions give the exact zero-loop test used by the sparse generator action.

## References

- Truth anchor: `D5/S3/Topology/CupCapComposition.composite_cupcap_mate`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_eq_zero_iff`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_pos`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_zero`
- Truth anchor: `D5/S3/Topology/CupCapComposition.reconnected`
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
