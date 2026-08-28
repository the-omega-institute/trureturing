# Linear Postprocessing Defect Contraction

## Abstract

Linear postprocessing contracts realization defect by its operator norm.

**Theorem 1.1 (Postprocessing contracts distance to the realizable image).**

$$\begin{gathered}\forall Y, Z: \operatorname{Type},\\{}[\operatorname{NormedAddCommGroup}(Y)] [\operatorname{NormedSpace}_{\mathbb{R}}(Y)] [\operatorname{FiniteDimensional}_{\mathbb{R}}(Y)],\\{}[\operatorname{NormedAddCommGroup}(Z)] [\operatorname{NormedSpace}_{\mathbb{R}}(Z)],\\{}B: \operatorname{ContinuousLinearMap}(\mathbb{R}, Y, Z), I: \operatorname{Set}(Y), y: Y,\\{}(\operatorname{IsClosed}(I) \land \operatorname{Nonempty}(I)) \Rightarrow\\{}(\operatorname{infDist}(B(y), \operatorname{image}(B, I)) \leq \left\lVert B \right\rVert \operatorname{infDist}(y, I)) \land\\{}(\left\lVert B \right\rVert \leq 1 \Rightarrow \operatorname{infDist}(B(y), \operatorname{image}(B, I)) \leq \operatorname{infDist}(y, I)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DefectComposition/LinearPostprocessingDefectContraction.linear_postprocessing_defect_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target are real normed spaces, with the source finite dimensional. The realizable set I is nonempty and closed, and B is a continuous linear postprocessor.

Closedness supplies a nearest realizable point to y. Its image under B is an admissible comparison point in image(B,I), and the operator norm bounds the resulting distance.

The source also assumes convexity and finite dimensionality of the target. Neither is needed for this conclusion, so the machine statement proves the two public clauses without them.

## References

- Truth anchor: `D5/S3/Observer/DefectComposition/LinearPostprocessingDefectContraction.linear_postprocessing_defect_contraction`
