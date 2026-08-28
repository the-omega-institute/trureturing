# Measurable Deficiency Triangle

## Abstract

One-way deficiency of arbitrary measurable statistical experiments satisfies the triangle inequality under Markov simulator composition.

**Theorem 1.1 (Measurable experiment deficiency obeys the triangle inequality).**

$$\begin{gathered}\forall Theta, X, Y, Z: \operatorname{Type},\\{}\operatorname{MeasurableSpace}\left(Theta\right), \operatorname{MeasurableSpace}\left(X\right), \operatorname{MeasurableSpace}\left(Y\right), \operatorname{MeasurableSpace}\left(Z\right),\\{}E: \operatorname{Kernel}\left(Theta, X\right), \operatorname{IsMarkovKernel}\left(E\right),\\{}F: \operatorname{Kernel}\left(Theta, Y\right), \operatorname{IsMarkovKernel}\left(F\right),\\{}G: \operatorname{Kernel}\left(Theta, Z\right), \operatorname{IsMarkovKernel}\left(G\right) \Rightarrow\\{}\operatorname{measurableDeficiency}\left(G, E\right) \leq \operatorname{measurableDeficiency}\left(G, F\right) + \operatorname{measurableDeficiency}\left(F, E\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle.measurable_deficiency_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The one-way deficiency is constructed as the infimum over Markov simulators of the supremum, over parameter states, of measurable-event total variation.

Two simulators compose. The measure-level triangle inequality separates their errors, while a layer-cake argument proves that applying the second Markov kernel contracts total variation. The pointwise estimate then passes through the supremum and the two independent infima.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle.measurable_deficiency_triangle`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](../DataProcessing/MeasurablePostprocessingDefectContraction.md)
