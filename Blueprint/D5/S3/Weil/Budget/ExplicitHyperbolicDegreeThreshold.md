# Explicit Hyperbolic Degree Threshold

## Abstract

A closed natural cutoff makes a faster positive hyperbolic orbit dominate a bounded tail.

**Theorem 1.1 (The faster hyperbolic orbit dominates beyond a closed cutoff).**

$$\begin{aligned}N_{0} = \left\lfloor\operatorname{max}(\frac{1}{\kappa_{0}}, \frac{2 \cdot C}{\Delta^{2} \cdot (\kappa_{0} - \kappa_{1})})\right\rfloor + 1,\\\forall \kappa_{0}, \kappa_{1}, \Delta, C \in \mathbb{R}, N \in \mathbb{N},\\0 < \kappa_{1} < \kappa_{0} \land 0 < \Delta \land 0 \le C \land N_{0} \le N \Rightarrow\\C \cdot \operatorname{sinh}(N \cdot \kappa_{1})^{2} < \Delta^{2} \cdot \operatorname{sinh}(N \cdot \kappa_{0})^{2}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold.explicit_hyperbolic_degree_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff is the natural floor of the larger of two explicit real bounds, plus one. The reciprocal-rate term forces the target argument above one, while the coefficient term makes the exponential rate gap absorb the nonnegative tail constant.

The proof first derives the two-sided estimate (exp(x)-1)/2 <= sinh(x) <= exp(x)/2 for positive x. It then uses exp(x)/4 <= sinh(x) for x at least one and the elementary strict bound x < exp(x) to compare the squared terms.

For kappa-zero = 1, kappa-one = 1/2, delta = 1, and C = 100, the formal cutoff evaluates to 401. The module verifies the strict comparison at degrees 401 and 402, and proves that the same comparison is false at degree one.

## References

- Truth anchor: `D5/S3/Weil/Budget/ExplicitHyperbolicDegreeThreshold.explicit_hyperbolic_degree_threshold`
