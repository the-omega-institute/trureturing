# Proper-stage continuous preimage obstruction

## Abstract

The original proper-stage signed laws forbid continuous clopen separation of the two original source pools.

**Theorem 1.1 (Original proper F forces finite clopen visits or misses).**

$$\forall inputs \in ProperOriginalDiracLiftInputs,\; \operatorname{OriginalLawsAndAllNDiracReadback}\left(inputs\right) \Rightarrow \left(\forall Dc \in \operatorname{Clopens}\left(\operatorname{StageSpace}\left(inputs\right)\right),\; \operatorname{Finite}\left(\operatorname{VisitsAlongOriginalJ}\left(inputs, Dc\right)\right) \lor \operatorname{Finite}\left(\operatorname{MissesAlongOriginalJ}\left(inputs, Dc\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.proper_F_clopen_dichotomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

ProperOriginalDiracLiftInputs consists exactly of l, H : Prefix l, D : H.Data, its original Laws, r,d,c in Coord l with omega <= r, r < c and d < c, and a whole point sequence z in H.Space(c). For every n the original D.nu(r,d,n) is the signed Dirac at the actual projection H.map(r,c,z(n)). No split, replacement J, pool or final-history premise is present. VisitsAlongOriginalJ is {n in D.J(r,d,c) | z(n) in Dc}; MissesAlongOriginalJ uses the complement. For every actual clopen Dc at that proper stage, one of those two sets is finite. The proof selects the entire Dirac lift, then invokes the original every-selection F law. Testing weak-star convergence at the continuous clopen indicator excludes two infinite sets of opposite values by epsilon one-third. This result is consumed below after original B/C/DJ preserve both source pools across a finite error. It is not final-stage F or an assumed finite-image law.

**Theorem 1.2 (No continuous separation of a historical J replacement).**

$$\forall inputs \in ProperStageInputs,\; \operatorname{OriginalLawsAndDiracReadback}\left(inputs\right) \Rightarrow \left(\forall f \in \operatorname{ContinuousMap}\left(\operatorname{ClosedDomain}\left(inputs\right), \operatorname{StageSpace}\left(inputs\right)\right),\; \forall C \in \operatorname{Clopens}\left(\operatorname{StageSpace}\left(inputs\right)\right),\; \operatorname{Not}\left(\operatorname{AllSourceImagesIn}\left(inputs, f, C, false\right) \land \operatorname{AllSourceImagesOutside}\left(inputs, f, C, true\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.no_continuous_pool_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

ProperStageInputs abbreviates precisely the theorem's parameters: an ordinal l, an actual SignedProperLimit.Prefix H l, D : H.Data and its Laws, r,d,b,c in Coord l, omega <= r, r < b, d < b and b <= c. The Bool-indexed pools M are contained in the original reservoirs D.N(r,d,e), and the actual stored D.J(r,d,b) equals their union. A is any closed subset of H.Space(c), and x is a whole Nat-indexed point sequence in A. OriginalLawsAndDiracReadback includes the preceding facts and, for every natural n, the equality of the original D.nu(r,d,n) with the signed Dirac at H.map(r,c,x(n)). It includes all of the existing Laws, with every-selection F; no common measure is chosen before the sequence. The conclusion says that for any continuous f : A -> H.Space(c) and any clopen C, the images f(x(n)) cannot all lie in C on M(false) and all lie outside C on M(true). Neither pool is assumed infinite: their intersections with the later J are proved infinite from the original laws.

The continuous set preimage of C is relatively clopen in the closed domain. Compact zero-dimensional separation extends it to an ambient clopen Dc. DJ makes the later J almost contained in the two pools. After deleting its actual finite error, original C and disjoint original reservoirs B give two infinite intersections with this same J. The selected Dirac lifts have norm one and push to the original source sequence for every n, including indices outside the pools. Proper-stage F then provides a weak-star limit. Evaluation at the continuous clopen indicator gives convergence of values which are one and zero on the two infinite pools. Epsilon one-third contradicts that convergence.

This is a local obstruction for the continuous finite-image argument on the same signed history. It neither constructs a raw history nor asserts the occurrence of a delayed event. The final application must obtain the actual replacement and whole-fibre clopen from the same executed delayed-successor witness and reflect the ambient preimage to a later proper stage. Full CH construction, the final finite-image endpoint and official acceptance remain open.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.no_continuous_pool_separation`
- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.proper_F_clopen_dichotomy`
- Dependency: [D5/S3/Topology/InverseLimit/SignedBirthEnumeration](SignedBirthEnumeration.md)
