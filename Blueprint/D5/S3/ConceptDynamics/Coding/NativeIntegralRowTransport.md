# Two-sign integer coordinate transport on the original row colimit

## Abstract

Two-sign integer coordinate transport on the original row colimit.

Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.

**Definition 1.1 (Retain both C2 coefficients with the original row orientation).**

$$\forall q \in Nat,\; \operatorname{IntLinearEquiv}\left(\operatorname{ExpandedRow}\left(q\right), \operatorname{NativeRow}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.basisEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sign is Multiplicative Bool with XOR addition, identity ofAdd false and tau=ofAdd true. ExpandedRow q=(Fin q times Sign)->Int; NativeRow q=VertexModule Sign q=Fin q->MonoidAlgebra Int Sign. basisEquiv sends v to the row i |-> single 1 (v(i,1)) + single tau (v(i,tau)). Its inverse reads every coefficient (z i).coeff h. decode_encode and encode_decode recover both coordinates; no plus/minus quotient, rationalization or integral splitting is used. The formula displays the definition's equivalence type for every natural q.

**Theorem 1.2 (Conjugate the actual integer row transition to the native transition).**

$$\forall q \in Nat, M \in \operatorname{GroupMat}\left(Sign, q, q\right),\; \forall v \in \operatorname{ExpandedRow}\left(q\right),\; \operatorname{basisEquiv}\left(q\right)\left(\operatorname{rowTransition}\left(M\right)\left(v\right)\right) = \operatorname{transition}\left(M\right)\left(\operatorname{basisEquiv}\left(q\right)\left(v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.transport_transition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M : GroupMat Sign q q is an arbitrary natural-coefficient group matrix. expansionMatrix M (i,h) (j,t) is the integer cast of (M i j).coeff(h inverse * t). rowTransition M is its toLinearMapRight', the row map v |-> v B, not a transpose. actual_expansion_adjacency on each native vertex basis extends by linearity to every integral row. transport_power and inverse_transport_power give the same intertwining for every natural power.

**Definition 1.3 (Transport every original stage, with both inverse identities).**

$$\forall q \in Nat, M \in \operatorname{GroupMat}\left(Sign, q, q\right),\; \operatorname{IntLinearEquiv}\left(\operatorname{ExpandedLimit}\left(M\right), \operatorname{DimensionGroup}\left(M\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.limitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ExpandedLimit M is StationaryModule(rowTransition M); DimensionGroup M is the existing StationaryModule(transition M). Module.DirectLimit.map of basisEquiv at each natural stage constructs toNativeLimit, and its inverse constructs fromNativeLimit. For every n:Nat and expanded row v, toNativeLimit(stage n v)=native stage n (basisEquiv v); the inverse has the corresponding same-stage formula for every native row. limits_left_inverse and limits_right_inverse yield limitEquiv. This is coefficient transport on the same original integer colimits, not yet a geometric beam action.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.basisEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.limitEquiv`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/NativeIntegralRowTransport.transport_transition`
- Dependency: [D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy](InertGroupBlockConjugacy.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNumberedHistories](ResetNumberedHistories.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/StandardBeamColimitCuts](StandardBeamColimitCuts.md)
