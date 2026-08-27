# Static Effect And Sequential Law Separation

## Abstract

Equal instrument effects do not determine sequential outcome laws.

**Theorem 1.1 (Equal effects can yield different two-step weights).**

$$\begin{gathered}P_{0}: QubitMatrix = basisZeroDensity, P_{1}: QubitMatrix = I - P_{0};\\{}K^{L}_{a}: QubitMatrix = \operatorname{if}\left(a, P_{1}, P_{0}\right), a: Bool;\\{}K^{J}_{a}: QubitMatrix = qubitX \cdot K^{L}_{a}, a: Bool;\\{}E^{M}_{a}: QubitMatrix = {M_{a}}^{*} \cdot M_{a}, M: Bool \to QubitMatrix, a: Bool;\\{}\mathcal{I}^{M}_{a}(\rho): QubitMatrix = M_{a} \cdot \rho \cdot {M_{a}}^{*}, M: Bool \to QubitMatrix, a: Bool, \rho: QubitMatrix;\\{}(\forall a: Bool, E^{L}_{a} = E^{J}_{a}) \land\\{}\sum_{a \in Bool} E^{L}_{a} = I \land\\{}\sum_{a \in Bool} E^{J}_{a} = I \land\\{}\operatorname{bornProbability}\left(\mathcal{I}^{L}_{false}(P_{0}), P_{1}\right) = 0 \land\\{}\operatorname{bornProbability}\left(\mathcal{I}^{J}_{false}(P_{0}), P_{1}\right) = 1.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.same_effects_different_two_step_joint_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Boolean-outcome qubit instruments are constructed explicitly. The first measures the computational projections, while the second applies the canonical bit flip after the same coordinate branch.

Their effect matrices agree outcome by outcome and both effect families sum to the identity. Starting from the basis-zero density after the false branch, however, the complementary second effect has weight zero for the projective instrument and weight one for the flipped instrument.

The branch maps and effect maps are displayed from their Kraus formulas. Thus the static agreement and sequential separation use the same constructed instruments rather than independent witnesses.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation.same_effects_different_two_step_joint_law`
- Dependency: [D5/S3/Observer/StateNotPath](../../Observer/StateNotPath.md)
