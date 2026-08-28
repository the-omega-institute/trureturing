# Measurable Descent Error Bounds

## Abstract

The best measurable Markov descent error is bounded below by half the observable fiber defect and above by that defect when measurable representatives exist.

**Theorem 1.1 (Best measurable descent error lies between half and all of the fiber defect).**

$$\begin{gathered}\forall X, B: \operatorname{Type},\\{}\operatorname{MeasurableSpace}\left(X\right), \operatorname{MeasurableSpace}\left(B\right),\\{}K: \operatorname{Kernel}\left(X, X\right), \operatorname{IsMarkovKernel}\left(K\right),\\{}q: X \to B, \operatorname{Measurable}\left(q\right) \Rightarrow\\{}\frac{\operatorname{observableKernelDefect}\left(K, q\right)}{2} \leq \operatorname{bestMeasurableDescentError}\left(K, q\right) \land \forall rep: B \to X, \operatorname{Measurable}\left(rep\right) \Rightarrow (\forall x: X, q(rep(q(x))) = q(x)) \Rightarrow \operatorname{bestMeasurableDescentError}\left(K, q\right) \leq \operatorname{observableKernelDefect}\left(K, q\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurableDescentErrorBounds.best_measurable_descent_error_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every candidate Markov kernel on the observable carrier, the measure-level triangle inequality bounds each same-fiber pair distance by twice its uniform descent error. Suprema over pairs and the infimum over candidates give the lower bound.

A measurable representative map pulls the observed-law kernel back to the observable carrier. Its error at each source state is one of the same-fiber distances, which proves the conditional upper bound.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableDescentErrorBounds.best_measurable_descent_error_bounds`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](MeasurablePostprocessingDefectContraction.md)
