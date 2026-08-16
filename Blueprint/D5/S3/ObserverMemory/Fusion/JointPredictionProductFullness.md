# Joint Prediction Product Fullness

## Abstract

Joint prediction fills the product exactly when every pair of prediction fibers meets.

**Theorem 1.1 (Joint prediction product fullness criterion).**

$$\forall Y, Z_{1}, Z_{2}, Z_{12},\ [\operatorname{Finite} Y] [\operatorname{Finite} Z_{1}] [\operatorname{Finite} Z_{2}] [\operatorname{Finite} Z_{12}],\ realize: Y \to Z_{12}, first: Y \to Z_{1}, second: Y \to Z_{2}, joint: Z_{12} \to Z_{1} \times Z_{2},\ \operatorname{Surjective}\left(realize\right) \Rightarrow \operatorname{Injective}\left(joint\right) \Rightarrow (\forall state, joint(realize(state)) = (first(state), second(state))) \Rightarrow\ ((\operatorname{Surjective}\left(joint\right) \iff \forall z1, z2,\ \exists state, first(state) = z1 \land second(state) = z2) \land\ (\operatorname{Surjective}\left(joint\right) \iff \operatorname{card}(Z_{12}) = \operatorname{card}(Z_{1}) \times \operatorname{card}(Z_{2}))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Fusion/JointPredictionProductFullness.joint_prediction_product_fullness_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite realized state type map surjectively onto a fused state type, and let an injective joint prediction map send each fused state to its two component predictions. The joint map is surjective exactly when every pair of component prediction fibers has a common realizing state.

For finite state spaces, injectivity turns product fullness into an exact cardinality test: the fused state count equals the product of the component state counts. Pinned Mathlib supplies the exact cardinality bridge Nat.bijective_iff_injective_and_card and the product identity Nat.card_prod. Direct local source search found these declarations; local smart-search returned no declarations, Loogle returned zero shaped matches, and LeanSearch's API endpoint returned HTTP 404.

The theorem proves compatibility fullness for two finite prediction coordinates. It does not assert probabilistic independence, an entropy identity, or a decomposition for more than two factors.

## References

- Truth anchor: `D5/S3/ObserverMemory/Fusion/JointPredictionProductFullness.joint_prediction_product_fullness_criterion`
