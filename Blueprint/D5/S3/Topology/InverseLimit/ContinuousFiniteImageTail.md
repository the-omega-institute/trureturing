# Continuous finite images on the actual CH limit

## Abstract

CH gives finite continuous disjoint images and both copy obstructions on the same constructed limit space.

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

This is a local obstruction for the continuous finite-image argument on the same signed history. It neither constructs a raw history nor asserts the occurrence of a delayed event. The final application must obtain the actual replacement and whole-fibre clopen from the same executed delayed-successor witness and reflect the ambient preimage to a later proper stage. The final application below obtains these inputs from the actual CH recursion on its literal final carrier.

**Theorem 1.3 (Finite images and copy obstructions on the actual CH limit).**

$$\forall hCH \in ContinuumEqualsAlephOne,\; \operatorname{ContinuousDisjointFiniteImage}\left(\operatorname{ActualFinalLimit}\left(hCH\right)\right) \land \left(\operatorname{FiniteDisjointHomeomorphicClosedSubspaces}\left(\operatorname{ActualFinalLimit}\left(hCH\right)\right) \land \operatorname{NoNonemptyCompactBinaryCopyTower}\left(\operatorname{ActualFinalLimit}\left(hCH\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.actual_CH_finite_image_and_copy_obstructions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tomasz Kania and Jerzy Kakol (2026). *Talagrand compacta, 2DCP, and pointwise quotients*. URL: <https://arxiv.org/abs/2607.06808v2>.

*Commentary.*

The sole premise is hCH : continuum = aleph_1. K is exactly SignedOrdinalRealization.finalPrefix(hCH).LimitSpace in all three clauses. For every closed A in K and continuous f : A -> K with A disjoint from range(f), range(f) is finite. For every closed A and every B in K, a homeomorphism A to B and disjointness imply both sets are finite; B need not be separately assumed closed. There is no sequence T(n) of nonempty compact subsets of this K such that every T(n) contains two disjoint subspaces each homeomorphic to T(n+1).

For an infinite disjoint image, ContinuousFiniteImageCapture.exists_original_dirac_capture is applied to the original wholeBirth U, V, nu and B tables. Its universal launch premise follows for every ordinary reservation from execute, scheduledLaunch, the actual prepared launch_eq, and coherent whole-birth transport. The capture gives a single whole point sequence x, one birth theta, two fixed source and target labels, disjoint birth support clopens, and all-natural-index Dirac and source-null equalities. Only top_read transports this whole pack to the corresponding original run birth. whole_birth_delayed_cofinal selects a single a, D, R and certificate for those original supports and labels. Matches and prepared_measure_read identify D.y with the projected original f(x(n)) by Dirac injectivity, for every n. No subsequence or fresh labels are introduced.

The same certificate provides its two infinite pools M(0), M(1) and a clopen whose entire old-coordinate fibers have opposite membership. successorHomeomorph, the equality selected = delayed(D,R,certificate), and selected_projection pull this very clopen back to K. successor_J identifies its source J with the union of these same pools. reservoir_incoming and the certificate's oldN inclusions retain the original permanent source reservoirs. The ambient clopen preimage is reflected to a later proper slice of this same finalPrefix. properData, properLaws, slice_nu, slice_J and slice_N supply exactly the original readbacks. final_no_continuous_pool_separation applies the all-n source Dirac lift and original F law to contradict the two surviving infinite pools. This proves the finite-image clause. finite_disjoint_homeomorphic_of_finite_image and no_compact_binary_copy_tower_of_finite_image give the remaining clauses on the identical K.

This theorem supplies the continuous finite-image and two copy-obstruction components of the CH construction. It does not combine the remaining Banach-space and global problem components into a total CH problem theorem.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.actual_CH_finite_image_and_copy_obstructions`
- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.no_continuous_pool_separation`
- Truth anchor: `D5/S3/Topology/InverseLimit/ContinuousFiniteImageTail.proper_F_clopen_dichotomy`
- Dependency: [D5/S3/Topology/InverseLimit/ContinuousFiniteImageCapture](ContinuousFiniteImageCapture.md)
- Dependency: [D5/S3/Topology/InverseLimit/CountableClopenReflection](CountableClopenReflection.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedBirthEnumeration](SignedBirthEnumeration.md)
- Dependency: [D5/S3/Topology/InverseLimit/SignedOrdinalRealizationEvents](SignedOrdinalRealizationEvents.md)
- Dependency: [D5/S3/Topology/Separation/DisjointCopyTower](../Separation/DisjointCopyTower.md)
