# Physical router profiles

## Abstract

Active literal router profiles distinguish every loaded address exactly when all deepest routers are active.

**Definition 1.1 (Internal router coordinates).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.Router`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.Router` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Router zero is empty. At a successor, none denotes the root router and some(b,v) denotes v in the right child when b is true and the left child otherwise. routerLabel reads the router field of the actual nested Tree. Incident and output rails are excluded. This indexes every internal router, including those off the programmed path.

**Definition 1.2 (Deepest physical router).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.deepest`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.deepest` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

snoc appends a final bit to the existing head-first Address. deepest n u is the actual depth-n router reached by the length-n prefix u. In the fully programmed tree for snoc u b, its label at deepest n i is encode b if i equals u and wait otherwise. Siblings snoc u false and snoc u true agree at every other internal router. Both statements hold at every natural n.

**Definition 1.3 (Actual sequential loading).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

loadedLabel reads routerLabel after load n n on loading n a bus zero. The existing sequential-loading identity identifies this tree with programmed n a n, for every external qutrit bus label. Thus no bus label affects the observed router profile.

**Definition 1.4 (Active profile equality).**

Lean statement: `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile`

*Formalization.* `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rate q is an arbitrary function on all internal routers. A router is active precisely when its rate is less than one. SameProfile requires equality of loadedLabel at every active router, allowing the two bus labels to differ. Separates means that this equality always forces the two addresses to coincide.

**Theorem 1.5 (Exact physical profile separation criterion).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n + 1\right) \to Real,\; \left(\forall a \in \operatorname{Address}\left(n + 1\right),\; \forall aPrime \in \operatorname{Address}\left(n + 1\right),\; \forall bus \in Qutrit,\; \forall busPrime \in Qutrit,\; \left(\forall v \in \operatorname{Router}\left(n + 1\right),\; q\left(v\right) < 1 \Rightarrow \operatorname{loadedLabel}\left(n + 1, a, bus, v\right) = \operatorname{loadedLabel}\left(n + 1, aPrime, busPrime, v\right)\right) \Rightarrow a = aPrime\right) \Leftrightarrow \left(\forall u \in \operatorname{Address}\left(n\right),\; q\left(\operatorname{deepest}\left(n, u\right)\right) < 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannRouterProfiles.profile_separation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive tree depth n+1, all addresses are distinguished exactly when every depth-n router has rate less than one. Necessity uses two siblings under an inactive deepest router: every other literal router label agrees. Sufficiency observes the deepest router under the first address prefix. Different prefixes give an occupied label versus wait; equal prefixes give the two encoded final bits. No restriction on the real rates is needed for this combinatorial equivalence, so independent rates in the closed unit interval and both endpoints are included. The statement concerns the actual loaded physical coordinates. It does not assert record independence, Gram rank or kernel, simplex optimization, or a noisy-continuation formula.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.Router`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.SameProfile`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.deepest`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.loadedLabel`
- Truth anchor: `D5/S3/Quantum/Routing/HannRouterProfiles.profile_separation_iff`
- Dependency: [D5/S3/Quantum/Routing/HannSpatialQram](HannSpatialQram.md)
