# Polynomial moment perturbation of real probability laws

## Abstract

An adjugate tilt preserves low-order moments and separates Gaussian weak limits.

**Definition 1.1 (Triangular window).**

$$\forall x : \mathbb{R}, \operatorname{window}\left(x\right) : \mathbb{R} = \operatorname{max}\left(1-\left|x\right|, 0\right)$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The window vanishes outside the closed unit interval.

**Definition 1.2 (Windowed Gram matrix).**

$$\begin{aligned}\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{gram}\left(R, \mu\right) : \operatorname{Matrix}\left(\operatorname{Fin}\left(R+1\right), \operatorname{Fin}\left(R+1\right), \mathbb{R}\right),\\\forall i,j : \operatorname{Fin}\left(R+1\right), \operatorname{gram}\left(R, \mu, i, j\right) = \int \operatorname{window}\left(x\right) \cdot x^{i.val+j.val} d\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.gram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry is the windowed inner product of the two indexed monomials.

**Definition 1.3 (Bounded continuous perturbation).**

$$\begin{aligned}\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{perturbation}\left(R, \mu\right) : \mathbb{R}\to^{b}\mathbb{R},\\\operatorname{let} c = \operatorname{mulVec}\left(\operatorname{adjugate}\left(\operatorname{gram}\left(R, \mu\right)\right), i \mapsto \int \operatorname{window}\left(x\right) \cdot x^{i.val+\left(R+1\right)} d\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right)\right),\\\forall x : \mathbb{R}, \operatorname{perturbation}\left(R, \mu, x\right) = \operatorname{det}\left(\operatorname{gram}\left(R, \mu\right)\right) \cdot \operatorname{window}\left(x\right) \cdot x^{R+1} - \sum_{j : \operatorname{Fin}\left(R+1\right)} \left(\operatorname{c}\left(j\right) \cdot \operatorname{window}\left(x\right) \cdot x^{j.val}\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.perturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here c is the adjugate of the Gram matrix applied to the vector of cross moments.

**Definition 1.4 (Real density).**

$$\begin{aligned}\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall x : \mathbb{R}, \operatorname{density}\left(R, \mu, x\right) : \mathbb{R},\\\operatorname{let} c = \operatorname{mulVec}\left(\operatorname{adjugate}\left(\operatorname{gram}\left(R, \mu\right)\right), i \mapsto \int \operatorname{window}\left(x\right) \cdot x^{i.val+\left(R+1\right)} d\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right)\right),\\\operatorname{density}\left(R, \mu, x\right) = 1+\frac{1}{2 \cdot \left(1+\left(\left|\operatorname{det}\left(\operatorname{gram}\left(R, \mu\right)\right)\right|+\sum_{j : \operatorname{Fin}\left(R+1\right)} \left|\operatorname{c}\left(j\right)\right|\right)\right)} \cdot \operatorname{perturbation}\left(R, \mu, x\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.density` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The denominator uses the sum of the absolute values of the residual coefficients.

**Definition 1.5 (Tilted probability law).**

$$\begin{aligned}\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{tilted}\left(R, \mu\right) : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right),\\\left(\operatorname{tilted}\left(R, \mu\right) : \operatorname{Measure}\left(\mathbb{R}\right)\right) = \operatorname{withDensity}\left(\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right), x \mapsto \operatorname{ENNReal.ofReal}\left(\operatorname{density}\left(R, \mu, x\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.tilted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The density integrates to one with respect to the baseline.

**Definition 1.6 (Standard Gaussian probability law).**

$$\operatorname{standardGaussian} : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \left(\operatorname{standardGaussian} : \operatorname{Measure}\left(\mathbb{R}\right)\right) = \operatorname{gaussianReal}\left(0, 1\right)$$

*Formalization.* `D5/S3/Analytic/Probability/MomentPerturbation.standardGaussian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Gaussian has mean zero and variance one.

**Lemma 1.7 (Continuity of the density in the observation).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \operatorname{Continuous}\left(x \mapsto \operatorname{density}\left(R, \mu, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.continuous_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The density is an affine function of the bounded continuous perturbation.

**Theorem 1.8 (Uniform density bounds).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall x : \mathbb{R}, \left(\frac{1}{2} \leq \operatorname{density}\left(R, \mu, x\right)\right) \land \left(\operatorname{density}\left(R, \mu, x\right) \leq \frac{3}{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.density_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each windowed monomial has absolute value at most one. The scale bounds the resulting change of density in absolute value by one half.

**Theorem 1.9 (Exact cancellation of the signed change).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \forall p : \operatorname{Polynomial}\left(\mathbb{R}\right), \operatorname{natDegree}\left(p\right) \leq R \Rightarrow \int \operatorname{Polynomial.eval}\left(x, p\right) (\operatorname{density}\left(R, \mu, x\right) - 1) d\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_mul_density_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gram matrix times the correction vector equals the determinant times the cross-moment vector. Integrating the residual term against each monomial through the chosen degree yields precisely these equations. Linearity extends the cancellation to all polynomials through that degree.

The identity applies at singular Gram matrices as well. The signed integrand has compact support for every polynomial.

**Lemma 1.10 (Normalization).**

$$\forall R : \mathbb{N}, \forall \mu : \operatorname{ProbabilityMeasure}\left(\mathbb{R}\right), \int \operatorname{density}\left(R, \mu, x\right) d\left(\mu : \operatorname{Measure}\left(\mathbb{R}\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.integral_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the constant polynomial in the signed cancellation identity.

**Theorem 1.11 (Strict positivity of the Gaussian Gram matrix).**

$$\forall R : \mathbb{N}, \operatorname{PosDef}\left(\operatorname{gram}\left(R, \operatorname{standardGaussian}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.gaussian_gram_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic form is the expectation of the window times the square of the polynomial with the test vector as coefficients. A nonzero polynomial has a point of nonvanishing inside the open window. Continuity and positive Gaussian mass on each nonempty open interval make the expectation strictly positive.

**Theorem 1.12 (Weak continuity of the change of law).**

$$\forall R : \mathbb{N}, \operatorname{Continuous}\left(\mu \mapsto \operatorname{tilted}\left(R, \mu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.continuous_tilted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each coefficient depends continuously on the baseline through fixed bounded continuous moments, the determinant, the adjugate, and the positive scale denominator. For each bounded continuous test, the tilted integral is a finite linear combination of baseline integrals against fixed bounded continuous functions. This gives continuity for the weak topology on probability laws.

**Theorem 1.13 (A strict bounded continuous test for the Gaussian tilt).**

$$\begin{aligned}\forall R : \mathbb{N}, \left(\int \operatorname{perturbation}\left(R, \operatorname{standardGaussian}, x\right) d\left(\operatorname{standardGaussian} : \operatorname{Measure}\left(\mathbb{R}\right)\right) < \int \operatorname{perturbation}\left(R, \operatorname{standardGaussian}, x\right) d\left(\operatorname{tilted}\left(R, \operatorname{standardGaussian}\right) : \operatorname{Measure}\left(\mathbb{R}\right)\right)\right) \land\\\left(\operatorname{tilted}\left(R, \operatorname{standardGaussian}\right) \neq \operatorname{standardGaussian}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/MomentPerturbation.tilted_gaussian_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gaussian Gram determinant is positive, so the residual polynomial is nonzero. The perturbation itself has a strictly positive squared expectation. Its expectation increases by the positive scale times that squared expectation, which separates the two laws.

## References

- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.continuous_density`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.continuous_tilted`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.density`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.density_bounds`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.gaussian_gram_posDef`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.gram`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.integral_density`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.integral_eval_mul_density_sub_one`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.perturbation`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.standardGaussian`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.tilted`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.tilted_gaussian_separation`
- Truth anchor: `D5/S3/Analytic/Probability/MomentPerturbation.window`
