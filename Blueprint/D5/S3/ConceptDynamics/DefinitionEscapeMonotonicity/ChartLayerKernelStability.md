# Chart Layer Kernel Stability

## Abstract

Image-injective chart postprocessing preserves kernel-derived escape data and dimension.

**Theorem 1.1 (Image-injective chart layers preserve escape dimension).**

$$\begin{aligned}q_{k + 1} = h \circ q_{k}, \operatorname{InjOn}\left(h, \operatorname{range}\left(q_{k}\right)\right) \Rightarrow\\\operatorname{ker}\left(q_{k + 1}\right) = \operatorname{ker}\left(q_{k}\right) \land\\{}\operatorname{E}\left(\operatorname{ker}\left(q_{k + 1}\right)\right) = \operatorname{E}\left(\operatorname{ker}\left(q_{k}\right)\right) \land\\d_{esc}(\operatorname{E}\left(\operatorname{ker}\left(q_{k + 1}\right)\right)) \leq d_{esc}(\operatorname{E}\left(\operatorname{ker}\left(q_{k}\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/ChartLayerKernelStability.chart_layer_preserves_escape_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the next chart readout be a postprocessing h of the current readout. The only injectivity required of h is on values actually realized by the current readout.

The imported postprocessing kernel criterion gives equality of the two Setoid.ker relations. Any escape layer determined by that relation is therefore unchanged.

The source atom does not define d_esc. The Lean declaration treats the escape layer and its ordered dimension as abstract readouts; equality of the layer makes the dimension equal, hence in particular nonincreasing.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/ChartLayerKernelStability.chart_layer_preserves_escape_dimension`
- Dependency: [D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus](../../ObserverMemory/Refinement/PostprocessingKernelCalculus.md)
