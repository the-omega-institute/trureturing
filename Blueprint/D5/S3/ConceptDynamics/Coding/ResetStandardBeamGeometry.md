# Concrete even whole-ray images and their original native coordinates

## Abstract

Concrete even whole-ray images and their original native coordinates.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (The actual alternating construction belongs to the full domain).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \operatorname{hasType}\left(\operatorname{evenAut}\left(q, hq, he\right), \operatorname{ResetFullAut}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.evenAut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatPositive(q) means 0<q. ResetGraph q=expandedGraph(resetMatrix q), ResetHistory q=History(ResetGraph q), and ResetFullAut q=FullAut(ResetGraph q). The actual finite expanded vertices and numbered edges use their native discrete topologies. Alternating.reset_expanded_essential q hq supplies both edge directions for every positive q, including deterministic q=1.

evenAut q hq he uses resetAlternatingWholeRayHomeomorph from actual NumberedData with C=1+resetMatrix and the proved resetFiniteForgetting. reset_generic_H_eq_applyTable identifies it with the original forward table on every history, whose shift law proves membership. Positive Even q includes q=2 and never requires q>=3. hasType displays the definition's result type.

**Theorem 1.2 (At the unchanged cut, every numbered edge of 1+A contributes).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right), alpha \in \operatorname{History}\left(\operatorname{ResetGraph}\left(q\right)\right), n \in Int,\; \operatorname{endpointRow}\left(\operatorname{ResetGraph}\left(q\right), \operatorname{image}\left(\operatorname{homeomorph}\left(\operatorname{evenAut}\left(q, hq, he\right)\right), \operatorname{ray}\left(\operatorname{ResetGraph}\left(q\right), alpha, n\right)\right), n\right) = \operatorname{rightMultiply}\left(\operatorname{singleEndpoint}\left(\operatorname{ResetGraph}\left(q\right), alpha, n\right), \operatorname{expansionMatrix}\left(\operatorname{matrixOneAdd}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.even_image_endpointRow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

singleEndpoint is Pi.single (endpoint (ResetGraph q) alpha n) 1. matrixOneAdd(A) is (1 : GroupMat Sign q q)+A. endpointRow installs the Finite Parts instance derived by even_image_atCut. reset_even_same_cut_whole_rays decomposes the actual image into whole, pairwise disjoint rays indexed by full numbered outgoing C edges, each with the target of its own indexing edge. endpointRow_disjointUnion sums each contribution, and expandedEdgeFiberEquiv counts the actual edge numbers to identify adjacency with expansionMatrix. Thus multiplicity, source, target and absolute sign are all retained.

**Theorem 1.3 (The true ray shift induces true Theta, including negative cuts).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), alpha \in \operatorname{History}\left(\operatorname{ResetGraph}\left(q\right)\right), n \in Int,\; \operatorname{resetBeamCoordinate}\left(q, \operatorname{shiftImageRayBeam}\left(q, hq, alpha, n\right)\right) = \operatorname{Theta}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\left(\operatorname{resetBeamCoordinate}\left(q, \operatorname{resetRayBeam}\left(q, hq, alpha, n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.reset_actual_shift_ray_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

shiftImageRayBeam is the Beam whose actual set is shift (ResetGraph q) image of ray alpha n, with the AtCut witness at n-1 supplied by shift_ray. resetBeamCoordinate is beamCoordinate followed by resetRowLimitEquiv. That equivalence first uses equality of the graph's counted adjacency with expansionMatrix, then the full two-coefficient NativeIntegralRowTransport.limitEquiv.

An actual ray at ANY integer cut has coordinate intStage (transition(resetMatrix q)) n (vertex endpointSuffix endpointSign). shift_ray preserves that endpoint and sends n to n-1; intStage_shift gives the equality. Theta is induced by the row transition. The separate left group action groupAction(resetMatrix q) tau represents complement, not this construction of time shift.

**Theorem 1.4 (The actual even image gives id plus Theta at every original ray stage).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right), alpha \in \operatorname{History}\left(\operatorname{ResetGraph}\left(q\right)\right), N \in Nat,\; \operatorname{resetRowLimitEquiv}\left(q\right)\left(\operatorname{F}\left(\operatorname{ResetGraph}\left(q\right), \operatorname{resetEssential}\left(q, hq\right)\right)\left(\operatorname{resetFullBeamRepresentation}\left(q, hq, \operatorname{evenAut}\left(q, hq, he\right)\right)\left(\operatorname{objectGroup}\left(\operatorname{ResetGraph}\left(q\right), \operatorname{resetEssential}\left(q, hq\right), \operatorname{singleton}\left(\operatorname{ResetGraph}\left(q\right), \operatorname{resetRayBeam}\left(q, hq, alpha, \operatorname{intCast}\left(N\right)\right)\right)\right)\right)\right)\right) = \operatorname{endSum}\left(\operatorname{linearIdentity}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{Theta}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)\left(\operatorname{stage}\left(\operatorname{transition}\left(\operatorname{resetMatrix}\left(q\right)\right), N\right)\left(\operatorname{vertexOfPair}\left(\operatorname{endpoint}\left(\operatorname{ResetGraph}\left(q\right), alpha, \operatorname{intCast}\left(N\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.reset_fullBeam_even_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

resetEssential(q,hq) abbreviates Alternating.reset_expanded_essential q hq, vertexOfPair(p)=vertex p.1 p.2, intCast is the natural-to-integer coercion, and endSum is addition of Int-linear maps. The stage map is the original Module.DirectLimit.of.

The same-cut disjoint whole-ray theorem is consumed by even_image_tagged_group to equate the actual image singleton with its tagged numbered components. F evaluates those components, resetRowLimitEquiv transports their original stage, and native_transition_one_add computes transition(1+A) z=z+transition(A) z on the FULL Int[C2] row. This proves the actual fullBeam action formula, not a formula for an arbitrary End assigned the name rho. The whole-group conclusion is established in the owning root module.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.evenAut`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.even_image_endpointRow`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.reset_actual_shift_ray_coordinate`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry.reset_fullBeam_even_stage`
- Dependency: [D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport](NativeIntegralRowTransport.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories](ResetAlternatingHistories.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamCoordinates](StandardBeamCoordinates.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](StandardBeamHomeomorphisms.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamPushforward](StandardBeamPushforward.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardTaggedBeams](StandardTaggedBeams.md)
