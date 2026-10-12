# The full original geometric representation realizes id plus Theta exactly for even q

## Abstract

The full original geometric representation realizes id plus Theta exactly for even q.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Conjugate actual whole-set pushforward onto the original integer group).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{MonoidHom}\left(\operatorname{ResetFullAut}\left(q\right), \operatorname{IntLinearEquiv}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NatPositive(q)=0<q. ResetGraph q=expandedGraph(resetMatrix q), with the original numbered edges, absolute Sign=Multiplicative Bool anchor, and native discrete product/subtype topology. ResetFullAut q is EVERY history homeomorphism commuting with the original unit shift. Its membership has no assumed window, endpoint preservation or beam-action field.

nativeEquiv q hq composes the additive equivalences of beamRowEquiv and resetRowLimitEquiv, then uses Mathlib toIntLinearEquiv to express the same coordinate functions with the original native integer-module instance. beamRowEquiv is the equivalence whose maps F and J satisfy BOTH inverse identities for the actual Mathlib Grothendieck completion. resetRowLimitEquiv uses actual numbered adjacency and the two-sign coefficient transport to the original DimensionGroup(resetMatrix q).

The displayed MonoidHom is rho's exact result type. rho(h) is nativeEquiv composed with resetFullBeamRepresentation(h) and nativeEquiv inverse. The geometric action is whole Set.image, with quotient compatibility proved by conjugated parallel past splices. Functoriality and inverse use the actual homeomorphism composition and inverse. The group remains the original integral stationary colimit at its original right-row orientation; no sign sector or scalar model is substituted.

**Theorem 1.2 (The original unit left shift has image true Theta).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{linearMap}\left(\operatorname{rho}\left(q, hq\right)\left(\operatorname{unitShift}\left(\operatorname{ResetGraph}\left(q\right)\right)\right)\right) = \operatorname{resetTheta}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho_unitShift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

linearMap is the underlying e.toLinearMap of an Int-linear equivalence; endSum is addition of linear maps and linearIdentity is LinearMap.id. The actual shift is x_t -> x_(t+1). shift_ray sends the full cut-n ray onto the cut-(n-1) ray with the same endpoint. intStage_shift, including negative cut -1 from original stage zero, gives true resetTheta. The original native vertex basis and the direct-limit existence of a stage representative extend the equality to the entire DimensionGroup; native_hom_ext implements that argument with the original integer-module instance.

Complement is represented separately by the left action groupAction(resetMatrix q) tau. Complement changes the absolute sign while retaining the XOR label, suffix and edge number. It is distinct as a construction from time transition Theta, even though the two actual maps coincide for the deterministic one-suffix q=1 dynamics.

**Theorem 1.3 (Every positive even q realizes id plus Theta on the entire original group).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \operatorname{linearMap}\left(\operatorname{rho}\left(q, hq\right)\left(\operatorname{evenAut}\left(q, hq, he\right)\right)\right) = \operatorname{endSum}\left(\operatorname{linearIdentity}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{resetTheta}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The witness evenAut is built from the actual resetNumberedData and resetFiniteForgetting, and reset_generic_H_eq_applyTable identifies its generic H with the original finite forward table. The same-cut theorem supplies every numbered outgoing edge of C=1+resetMatrix as a disjoint whole-ray component, with arbitrary legal futures and the correct target endpoint.

On every original natural-stage vertex basis generator the actual image row is its basis row times expansionMatrix(1+A). Full coefficient transport gives transition(1+A)=id+transition(A). rho_even_basis computes this at every stage; the original vertex basis and direct-limit existence of a stage representative give the displayed equality on the ENTIRE original integer group. All positive Even q, including q=2, are included. No freely chosen algebraic End is installed as the action.

**Theorem 1.4 (Exact membership for every positive q).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \left(\exists h \in \operatorname{ResetFullAut}\left(q\right),\; \operatorname{linearMap}\left(\operatorname{rho}\left(q, hq\right)\left(h\right)\right) = \operatorname{endSum}\left(\operatorname{linearIdentity}\left(\operatorname{DimensionGroup}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{resetTheta}\left(q\right)\right)\right) \Leftrightarrow \operatorname{Even}\left(q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.reset_full_standard_representation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula is exactly forall q:Nat, forall hq:0<q, (exists h:ResetFullAut q, (rho q hq h).toLinearMap=LinearMap.id+resetTheta q) iff Even q. The existential ranges over the full group of actual unit-shift-commuting history homeomorphisms, using the same original DimensionGroup and original unit shift.

The even direction supplies evenAut and rho_even. If q is odd, including q=1, the explicit integral row w_i=(-1)^i(single 1 1-single tau 1) satisfies T w=-w and has coefficient (-1)^k at suffix zero after every future iterate. Its true original stage-zero colimit class survives and is killed by id+Theta. rho_odd_excluded applies reset_odd_killed_class directly: equality of rho(h).toLinearMap with id+resetTheta would give the nonzero killed class and zero equal images, contradicting rho(h).injective. This obstruction uses no transition-injectivity or torsion-free hypothesis.

Finite tagged actual beam copies cover the deterministic q=1 graph without an entropy premise. The literal-bit/reset-path coding uses the existing fallback p=1/2 there; the literature's q>=2 positive-entropy regime is not extended to q=1. The statement concerns this geometric integral representation and parity membership. It makes no claim of novelty, an entropy formula, a numerical application, an ordered-cone classification or an additional model theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.reset_full_standard_representation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho_even`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetFullStandardBeamRepresentation.rho_unitShift`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeOddObstruction](ResetNativeOddObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetStandardBeamGeometry](ResetStandardBeamGeometry.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamIdentification](StandardBeamIdentification.md)
