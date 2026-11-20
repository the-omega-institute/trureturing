# Polynomial moment perturbation of real probability laws

## Abstract

An adjugate tilt preserves low-order moments and separates Gaussian weak limits.

Fix a real Borel probability law and a natural order. The triangular window is max(1 minus the absolute value of the observation, 0). The Gram entry at row i and column j is the expectation of the window times the power i plus j. The cross-moment vector uses powers i plus R plus 1. Multiply that vector by the adjugate to obtain the correction coefficients.

The bounded continuous function h is the window times the residual polynomial. The residual has the Gram determinant as its coefficient of degree R plus 1 and the negatives of the correction coefficients in degrees 0 through R. Add one to the sum of the absolute values of these coefficients, double that quantity and take its reciprocal to obtain the scale. The tilted law has density one plus the scaled perturbation. The symbol gamma denotes the standard Gaussian and integrals use the underlying measures.

**Lemma 1.1 (Continuity of the density in the observation).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{Continuous}\left(x \mapsto \operatorname{density}\left(R, \mu, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.continuous_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is an affine function of the bounded continuous perturbation.

**Theorem 1.2 (Uniform density bounds).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall x : \mathbb{R}, \frac{1}{2} \leq \operatorname{density}\left(R, \mu, x\right) \land \operatorname{density}\left(R, \mu, x\right) \leq \frac{3}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.density_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each windowed monomial has absolute value at most one. The scale bounds the resulting change of density in absolute value by one half.

**Theorem 1.3 (Exact cancellation of the signed change).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall p : \operatorname{Polynomial}\left(\mathbb{R}\right), \operatorname{natDegree}\left(p\right) \leq R \Rightarrow \int \operatorname{eval}\left(p, x\right) (\operatorname{density}\left(R, \mu, x\right) - 1) d\mu = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_mul_density_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram matrix times the correction vector equals the determinant times the cross-moment vector. Integrating the residual term against each monomial through the chosen degree yields precisely these equations. Linearity extends the cancellation to all polynomials through that degree.

The identity applies at singular Gram matrices as well. The signed integrand has compact support for every polynomial.

**Lemma 1.4 (Normalization).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \int \operatorname{density}\left(R, \mu, x\right) d\mu = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.integral_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the constant polynomial in the signed cancellation identity.

**Theorem 1.5 (Preservation of integrable polynomial expectations).**

$$\begin{aligned}\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall p : \operatorname{Polynomial}\left(\mathbb{R}\right), \operatorname{natDegree}\left(p\right) \leq R \Rightarrow \operatorname{Integrable}\left(x \mapsto \operatorname{eval}\left(p, x\right), \mu\right) \Rightarrow\\\operatorname{Integrable}\left(x \mapsto \operatorname{eval}\left(p, x\right), \operatorname{tilted}\left(R, \mu\right)\right) \land \int \operatorname{eval}\left(p, x\right) d\operatorname{tilted}\left(R, \mu\right) = \int \operatorname{eval}\left(p, x\right) d\mu\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_tilted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density multiplies the baseline integrand by one plus the scaled correction. Its added part is integrable by compact support and has integral zero.

**Theorem 1.6 (Strict positivity of the Gaussian Gram matrix).**

$$\forall R : \mathbb{N}, \operatorname{PosDef}\left(\operatorname{gram}\left(R, \gamma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.gaussian_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form is the expectation of the window times the square of the polynomial with the test vector as coefficients. A nonzero polynomial has a point of nonvanishing inside the open window. Continuity and positive Gaussian mass on each nonempty open interval make the expectation strictly positive.

**Theorem 1.7 (Weak continuity of the change of law).**

$$\forall R : \mathbb{N}, \operatorname{Continuous}\left(\mu \mapsto \operatorname{tilted}\left(R, \mu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.continuous_tilted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coefficient depends continuously on the baseline through fixed bounded continuous moments, the determinant, the adjugate, and the positive scale denominator. For each bounded continuous test, the tilted integral is a finite linear combination of baseline integrals against fixed bounded continuous functions. This gives continuity for the weak topology on probability laws.

**Theorem 1.8 (A strict bounded continuous test for the Gaussian tilt).**

$$\forall R : \mathbb{N}, \int \operatorname{h}\left(R, \gamma, x\right) d\gamma < \int \operatorname{h}\left(R, \gamma, x\right) d\operatorname{tilted}\left(R, \gamma\right) \land \operatorname{tilted}\left(R, \gamma\right) \neq \gamma$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.tilted_gaussian_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gaussian Gram determinant is positive, so the residual polynomial is nonzero. The perturbation itself has a strictly positive squared expectation. Its expectation increases by the positive scale times that squared expectation, which separates the two laws.

## References

- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.continuous_density`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.continuous_tilted`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.density_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.gaussian_gram_posDef`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.integral_density`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_mul_density_sub_one`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_tilted`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.tilted_gaussian_separation`
