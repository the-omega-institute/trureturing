# Obstruction to Wang-Style Zero-Region Descent

## Abstract

Half-plane threshold positivity propagates automatically only toward narrower regions; strict threshold shrinkage alone does not supply Wang-style descent.

**Theorem 1.1 (Threshold positivity is monotone toward narrower regions).**

$$\forall mu: \mathbb{C} \to \mathbb{R}, \forall a, b\in\mathbb{R}, a \le b \Rightarrow (\operatorname{T}\left(mu, a\right) \Rightarrow \operatorname{T}\left(mu, b\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction.threshold_positivity_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If positivity holds to the right of 1/2 + a and a <= b, it also holds to the right of 1/2 + b. This is the automatic direction because the second half-plane is contained in the first.

**Theorem 1.2 (Strict threshold contraction does not imply descent).**

$$\exists mu: \mathbb{C} \to \mathbb{R}, F: \mathbb{R} \to \mathbb{R},\\\operatorname{T}\left(mu, \frac{1}{2}\right) \land \neg \operatorname{T}\left(mu, 0\right) \land (\forall a\in\mathbb{R}, 0 < a \Rightarrow \operatorname{F}\left(a\right) < a) \land\\\neg(\operatorname{T}\left(mu, \frac{1}{2}\right) \Rightarrow \operatorname{T}\left(mu, \operatorname{F}\left(\frac{1}{2}\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction.wang_style_descent_requires_analytic_input` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The explicit measurement mu(s) = Re(s) - 1 and contraction F(a) = a/2 satisfy positivity at a = 1/2 and F(a) < a for every positive a, but positivity fails both at zero and after the first descent step. Any valid descent theorem therefore requires an additional analytic gain.

## References

- Truth anchor: `D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction.threshold_positivity_mono`
- Truth anchor: `D5/S3/Analytic/Characterizations/ZeroRegionDescentObstruction.wang_style_descent_requires_analytic_input`
