# Both inverses between geometric completion and the original row colimit

## Abstract

Both inverses between geometric completion and the original row colimit.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Build the inverse from full vertex rays and signed integer sums).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{hasType}\left(\operatorname{J}\left(G, hG\right), \operatorname{IntLinearMap}\left(\operatorname{RowLimit}\left(G\right), \operatorname{BeamGroup}\left(G, hG\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

chosenRay u N is the entire ray at cut (N:Int) of vertexHistory G hG u N. chosenClass is its singleton image in the actual Mathlib completion. JStage N z is the FULL signed integer sum over u:V of z u times chosenClass u N. F_chosenClass identifies each actual generator with stage N (Pi.single u 1), and F_JStage extends to every integral row.

F_injective is derived from equivalent_iff_value_eq and the localization universal property. It proves JStage_compatible after the actual geometric generator calculation, not from an assumed lift field. The original Module.DirectLimit.lift then constructs J. Auxiliary history choices disappear through endpoint-preserving past splices and matching.

**Theorem 1.2 (F followed after J is identity on the whole original row colimit).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{compose}\left(\operatorname{intLinearMap}\left(\operatorname{F}\left(G, hG\right)\right), \operatorname{J}\left(G, hG\right)\right) = \operatorname{linearIdentity}\left(\operatorname{RowLimit}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.FJ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

compose is LinearMap.comp; intLinearMap(F) is F.toIntLinearMap. The exact equality is (F G hG).toIntLinearMap.comp (J G hG)=LinearMap.id on RowLimit G. Direct-limit hom_ext reduces it to every natural stage and every signed integer row, where F_JStage gives the identity.

**Theorem 1.3 (J followed after F is identity on the actual group completion).**

$$\forall V \in Type, E \in Type, G \in \operatorname{DirectedMultigraph}\left(V, E\right), finiteV \in \operatorname{Fintype}\left(V\right), finiteE \in \operatorname{Fintype}\left(E\right), decV \in \operatorname{DecidableEq}\left(V\right), hG \in \operatorname{Essential}\left(G\right),\; \operatorname{compose}\left(\operatorname{J}\left(G, hG\right), \operatorname{intLinearMap}\left(\operatorname{F}\left(G, hG\right)\right)\right) = \operatorname{linearIdentity}\left(\operatorname{BeamGroup}\left(G, hG\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.JF` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact equality is (J G hG).comp (F G hG).toIntLinearMap=LinearMap.id on BeamGroup G hG. Apply the previously derived F_injective to each completion element and then FJ. This handles all formal differences through Mathlib localization. beamRowEquiv is the resulting Int-linear equivalence with forward F and inverse J; neither direction is merely a promised isomorphism.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.FJ`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.J`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/StandardBeamIdentification.JF`
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardTaggedBeams](StandardTaggedBeams.md)
