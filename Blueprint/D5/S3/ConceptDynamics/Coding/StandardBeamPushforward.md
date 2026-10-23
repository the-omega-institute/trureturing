# Functorial whole-set image on the actual geometric completion

## Abstract

Functorial whole-set image on the actual geometric completion.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Push each entire beam through the actual homeomorphism).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), hG \in \operatorname{Essential}\left(G\right),\; \forall h \in \operatorname{FullAut}\left(G\right), A \in \operatorname{Object}\left(G\right),\; \operatorname{hasType}\left(\operatorname{imageObject}\left(G, hG, h, A\right), \operatorname{Object}\left(G\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.imageObject` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

imageObject keeps A.Tag and A.finiteTag, and sends beam i to imageBeam G hG h (A.beam i), whose set is h.val image of the WHOLE beam. hasType displays the definition's type. Image sets are beams by the compactness-derived window theorem. Tags retain identical copies. The intrinsic disjoint partition of a beam maps to a disjoint family because the actual h is injective. Coordinates add for these disjoint unions at a common cut.

**Theorem 1.2 (Actual image respects every geometric equivalence).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), hG \in \operatorname{Essential}\left(G\right),\; \forall h \in \operatorname{FullAut}\left(G\right), A \in \operatorname{Object}\left(G\right), Bobj \in \operatorname{Object}\left(G\right), he \in \operatorname{Equivalent}\left(G, A, Bobj\right),\; \operatorname{Equivalent}\left(G, \operatorname{imageObject}\left(G, hG, h, A\right), \operatorname{imageObject}\left(G, hG, h, Bobj\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.imageObject_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original common-cut Matching pairs actual ray pieces with equal endpoints. For each pair, parallel_image_coordinate uses conjugatePartsEquiv at n+a+b+d, whose individual restrictions are actual future-preserving splices. imageObject_value_partition sums these coordinates over every original tagged piece. Their equality and equivalent_iff_value_eq produce an actual eventual Matching of the images. No algebraic action, beam-image promise, colimit isomorphism or supplied window is a premise.

**Definition 1.3 (Functorial image gives an integral representation with the actual inverse).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), topV \in \operatorname{TopologicalSpace}\left(V\right), discreteV \in \operatorname{DiscreteTopology}\left(V\right), topE \in \operatorname{TopologicalSpace}\left(E\right), discreteE \in \operatorname{DiscreteTopology}\left(E\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{MonoidHom}\left(\operatorname{FullAut}\left(G\right), \operatorname{IntLinearEquiv}\left(\operatorname{BeamGroup}\left(G, hG\right), \operatorname{BeamGroup}\left(G, hG\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.fullBeamRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed MonoidHom is the result type of fullBeamRepresentation G hG. monoidImage descends imageObject to the geometric quotient. groupImage extends intoGroup composed with monoidImage by the Mathlib Grothendieck universal property. Set.image composition gives groupImage(g*h)=groupImage(g) composed with groupImage(h), and identity maps to identity.

groupImageEquiv uses groupImage(h inverse) as its inverse; both inverse laws follow from these composition identities and the actual homeomorphism inverse. Converting the additive equivalence to an Int-linear equivalence produces fullBeamRepresentation. On every original object generator its action is objectGroup(imageObject h A). This is a representation on the completed geometric integer group; identifying it with the native row group uses both identities in StandardBeamIdentification.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.fullBeamRepresentation`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.imageObject`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamPushforward.imageObject_equivalent`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms](StandardBeamHomeomorphisms.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardTaggedBeams](StandardTaggedBeams.md)
