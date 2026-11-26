# Posterior Total Variation and Conditional Gini Loss

## Abstract

The sharp finite-alphabet comparison between posterior total variation and conditional Gini loss.

Let p be a probability mass function, r the refined readout, t the target, and f the deterministic coarsening. M(p,r,d) is the refined fiber mass. T(p,r,t,f) is the sum over refined fibers of their real mass times the total variation between the two target posteriors. Each posterior coordinate is its joint target-and-fiber mass divided by the corresponding fiber mass, using totalized division in the extended nonnegative reals. A zero denominator gives zero. The ratios are converted to real coordinates before taking total variation. Total variation is half the finite sum of absolute coordinate differences. The outer sum ranges over all refined labels. L(p,r,t,f) is the coarse impurity minus the refined impurity in real coordinates. K(A) equals floor(n squared over four) divided by n for a target type A of cardinality n.

**Theorem 1.1 (Upper bound for mass-weighted posterior total variation).**

$$\begin{gathered}\forall X, C, D, A: \operatorname{Type}, [\operatorname{Fintype}(A)],\\{}p: \operatorname{PMF}(X), r: X \to D, t: X \to A, f: D \to C,\\{}2 \le \operatorname{card}(A) \Rightarrow \operatorname{T}(p, r, t, f)^{2} \le \operatorname{K}(A) \cdot \operatorname{L}(p, r, t, f).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/ConditionalGiniTV.weighted_posterior_totalVariation_sq_le_gini_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a positive-mass refined fiber both posteriors are normalized. Their difference has sum zero. Centering its positive sign indicator and applying Cauchy–Schwarz gives the factor k(n-k)/n for a sign set of size k. The maximum over k is K(A). Weighted Cauchy–Schwarz across refined fibers then gives the stated inequality using the exact conditional Gini defect. Zero-mass fibers disappear from the weighted sums.

**Theorem 1.2 (Two refined fibers attain the coefficient).**

$$\begin{gathered}\forall A: \operatorname{Type}, [\operatorname{Fintype}(A)], 2 \le \operatorname{card}(A) \Rightarrow\\{}\exists p: \operatorname{PMF}(A), r: A \to \operatorname{Bool},\\{}(\forall b: \operatorname{Bool}, \operatorname{M}(p, r, b) = \frac{1}{2}) \land \operatorname{T}(p, r, \operatorname{id}, \operatorname{const}) = \frac{1}{2} \land 0 < \operatorname{L}(p, r, \operatorname{id}, \operatorname{const}) \land\\{}\operatorname{T}(p, r, \operatorname{id}, \operatorname{const})^{2} = \operatorname{K}(A) \cdot \operatorname{L}(p, r, \operatorname{id}, \operatorname{const}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Information/ConditionalGiniTV.conditional_gini_tv_attained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use X equal to A, the identity target, and the constant map f from Bool to Unit. Split A into blocks of sizes floor(n/2) and n minus floor(n/2), assigning one half of the probability mass uniformly to each block. The refined readout reports the block. The coarse posterior is the half-mixture of both block posteriors. Each posterior total variation is one half. For a first block of size k, the defect is n divided by the product 4 k (n-k). Equality with positive defect forces every universal coefficient to be at least K(A).

## References

- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalGiniTV.conditional_gini_tv_attained`
- Truth anchor: `D5/S3/ConceptDynamics/Information/ConditionalGiniTV.weighted_posterior_totalVariation_sq_le_gini_defect`
- Dependency: [D5/S3/ConceptDynamics/Information/ConditionalGiniDefect](ConditionalGiniDefect.md)
- Dependency: [D5/S3/TotalVariation/Metric](../../TotalVariation/Metric.md)
