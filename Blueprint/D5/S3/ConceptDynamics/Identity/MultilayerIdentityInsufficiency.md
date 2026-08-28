# Multilayer Identity Insufficiency

## Abstract

A concrete two-layer cone loses its upper bit, and noninjective projections neither admit left inverses nor determine a unique fiber-constant assignment.

**Lemma 1.1 (The two-layer cone loses its upper bit).**

$$\operatorname{Nonempty}\left(\operatorname{CompatibleFamily}\left(twoLayerState, twoLayerProjection\right)\right) \land \left(\exists x \in \operatorname{CompatibleFamily}\left(twoLayerState, twoLayerProjection\right), y \in \operatorname{CompatibleFamily}\left(twoLayerState, twoLayerProjection\right),\; x_{0} = y_{0} \land x_{1} \ne y_{1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency.two_layer_cone_nonempty_and_loses_high_information` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete system has a one-point lower layer and a Boolean upper layer. Each Boolean value determines a compatible subject, so the space of compatible families is inhabited.

The subjects determined by false and true have the same lower component because the downward projection forgets the bit, while their upper components remain distinct. Thus lower-layer agreement does not recover the higher-layer state.

**Theorem 1.2 (A noninjective layer cannot recover or choose uniquely).**

$$\forall Sj \in Type, Si \in Type, Norm \in Type, p \in Sj \to Si, n1 \in Norm, n2 \in Norm,\; \left(\left(\neg \operatorname{Injective}\left(p\right)\right) \land n1 \ne n2\right) \Rightarrow \left(\left(\neg \left(\exists r \in Si \to Sj,\; \operatorname{LeftInverse}\left(r, p\right)\right)\right) \land \left(\exists q1 \in Sj \to Norm, q2 \in Sj \to Norm,\; \operatorname{FiberConstant}\left(p, q1\right) \land \left(\operatorname{FiberConstant}\left(p, q2\right) \land q1 \ne q2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency.noninjective_layer_cannot_recover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A left inverse would force the layer projection to be injective. Hence a noninjective projection admits no recovery map that reconstructs every higher-layer state.

When the normative codomain contains two distinct values, the two constant assignments to those values are both constant on every projection fiber. They are distinct legal assignments, so fiber compatibility alone does not select a unique high-level choice.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency.noninjective_layer_cannot_recover`
- Truth anchor: `D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency.two_layer_cone_nonempty_and_loses_high_information`
