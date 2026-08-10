# Weighted Path-Ratio Bound

## Abstract

The path contraction ratio is a weighted average of pointwise ratios and is bounded by their path supremum.

**Theorem 1.1 (Path contraction is a weighted average bounded by the path supremum).**

$$\begin{gathered}\frac{\operatorname{targetPath}(d)}{\operatorname{sourcePath}(d)}=\operatorname{weightedAverage}_{d}(\operatorname{pointwiseRatio}),\\\operatorname{targetPath}(d)\le\operatorname{pathSup}(d)\operatorname{sourcePath}(d).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/DivergenceSupport/PathRatioBound.path_ratio_weighted_average_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the input squared path speed be strictly positive on the unit interval. Assume the source weight and its product with the pointwise output-to-input speed ratio are interval integrable, the source path integral is positive, and the pointwise ratios are bounded above.

The output path integral equals the integral of pointwiseRatio times pathWeight. After division by sourcePath, this is the weighted average displayed above, with normalized weight pathWeight divided by sourcePath. Pointwise domination by pathSup and nonnegativity of the path weight give targetPath(d) <= pathSup(d) * sourcePath(d).

## References

- Truth anchor: `D5/S3/DivergenceSupport/PathRatioBound.path_ratio_weighted_average_and_bound`
