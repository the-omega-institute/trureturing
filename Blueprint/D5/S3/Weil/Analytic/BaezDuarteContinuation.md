# Baez-Duarte continuation through the pole

## Abstract

The original coefficient decay gives holomorphic Newton continuation, compact uniformity through one, and standard RH.

For every displayed statement, c is the existing real baezDuarte coefficient, cComplex its original complex finite sum, and P the existing normalizedPochhammer polynomial. H is the open half-plane Re(s)>1/2; F(s) is the tsum of term(s)(k)=c(k)P(k,s/2); partial(N,s) is the sum of these terms over range N. Decay(c) means: for every real epsilon>0 there are real C>0 and natural N>=1 such that for every k>=N, |c(k)|<=C*k^(-3/4+epsilon). For a complex coefficient sequence, Decay uses the complex norm. DecayHalf uses epsilon/2 instead. Compact(K) below means K is compact and K is a subset of H. All s and k are universally quantified in their stated domains. The entire multiplier riemannZetaOne is mathlib riemannZeta₁, and analyticReciprocal(s)=(s-1)/riemannZeta₁(s).

**Theorem 1.1 (Original finite coefficients).**

$$\operatorname{ofReal}\left(\operatorname{c}\left(k\right)\right)=\operatorname{cComplex}\left(k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_complex_finite_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The cast of the real coefficient equals the original complex binomial sum, using realness of zeta at the positive even integers. No decay hypothesis is needed.

**Theorem 1.2 (Pointwise absolute convergence).**

$$\operatorname{Decay}\left(c\right)\land s\in H\Rightarrow \operatorname{Summable}\left(\operatorname{term}\left(s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The existing compact majorant applied to a singleton proves summability of the actual Newton terms.

**Theorem 1.3 (Uniform convergence on every compact subset).**

$$\operatorname{Decay}\left(c\right)\land \operatorname{Compact}\left(K\right)\Rightarrow \operatorname{TendstoUniformlyOn}\left(partial, F, \operatorname{atTop}\left(\right), K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_uniform` (`✓ std3`). ∎

*Citation.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The range partial sums converge uniformly to their actual tsum on every compact subset of Re(s)>1/2. Empty compacts and all finite prefixes are retained.

**Theorem 1.4 (Locally uniform convergence).**

$$\operatorname{Decay}\left(c\right)\Rightarrow \operatorname{TendstoLocallyUniformlyOn}\left(partial, F, \operatorname{atTop}\left(\right), H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_locally_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Compact uniform convergence on the open half-plane supplies locally uniform convergence.

**Theorem 1.5 (Holomorphic Newton sum).**

$$\operatorname{Decay}\left(c\right)\Rightarrow \operatorname{DifferentiableOn}\left(\operatorname{Complex}\left(\right), F, H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_differentiable` (`✓ std3`). ∎

*Citation.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Each term is a polynomial in s, and the locally uniform limit is complex differentiable throughout the open half-plane.

**Theorem 1.6 (Regularized product identity).**

$$\operatorname{Decay}\left(c\right)\land s\in H\Rightarrow \operatorname{riemannZetaOne}\left(s\right) \operatorname{F}\left(s\right)=s-1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_regularized_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Analytic uniqueness continues the initial identity from a neighborhood of two to the connected half-plane. The entire multiplier is the public mathlib riemannZeta₁; zero-freeness is proved from the identity and is not a premise.

**Theorem 1.7 (The sum at one is zero).**

$$\operatorname{Decay}\left(c\right)\Rightarrow \operatorname{HasSum}\left(\operatorname{term}\left(1\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The analytic reciprocal has value zero at one. This is not the reciprocal of the totalized raw zeta value.

**Theorem 1.8 (The analytic reciprocal on the whole half-plane).**

$$\operatorname{Decay}\left(c\right)\land s\in H\Rightarrow \operatorname{HasSum}\left(\operatorname{term}\left(s\right), \frac{s-1}{\operatorname{riemannZetaOne}\left(s\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The actual Newton terms have sum (s-1)/riemannZeta₁(s), including at one.

**Theorem 1.9 (Raw reciprocal away from one).**

$$\operatorname{Decay}\left(c\right)\land s\in H\land s\neq 1\Rightarrow \operatorname{HasSum}\left(\operatorname{term}\left(s\right), \frac{1}{\operatorname{riemannZeta}\left(s\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_off_one` (`✓ std3`). ∎

*Citation.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Off one, the same series has sum 1/riemannZeta(s). No statement identifies the raw reciprocal with the analytic extension at one.

**Theorem 1.10 (Compact uniformity across the pole).**

$$\operatorname{Decay}\left(c\right)\land \operatorname{Compact}\left(K\right)\Rightarrow \operatorname{TendstoUniformlyOn}\left(partial, \operatorname{analyticReciprocal}\left(\right), \operatorname{atTop}\left(\right), K\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The range partial sums converge uniformly to the analytic reciprocal on every compact subset of the half-plane, including compacts that contain or cross one.

**Theorem 1.11 (Coefficient decay implies standard RH).**

$$\operatorname{Decay}\left(c\right)\Rightarrow \operatorname{RiemannHypothesis}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_decay_implies_rh` (`✓ std3`). ∎

*Citation.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The all-positive-epsilon bound on the actual coefficients excludes zeta zeros in the right half of the critical strip and applies the existing standard RH reduction. The necessity direction is a separate remaining obligation.

**Theorem 1.12 (Both epsilon conventions agree).**

$$\operatorname{Decay}\left(c\right)\iff \operatorname{DecayHalf}\left(c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_epsilon_half_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

Quantification over every positive epsilon makes the exponents -3/4+epsilon and -3/4+epsilon/2 equivalent. This says nothing about epsilon zero or the boundary line Re(s)=1/2.

**Theorem 1.13 (The original complex finite bound implies RH).**

$$\operatorname{Decay}\left(\operatorname{cComplex}\left(\right)\right)\Rightarrow \operatorname{RiemannHypothesis}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_original_decay_implies_rh` (`✓ std3`). ∎

*Citation.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

The same every-positive-epsilon decay bound, now on the norm of the original complex finite sum, implies standard RH. The exact coefficient cast binding converts this hypothesis to the real-coefficient sufficient direction.

**Theorem 1.14 (The raw zeta product away from the pole).**

$$\operatorname{Decay}\left(c\right)\land s\in H\land s\neq 1\Rightarrow \operatorname{riemannZeta}\left(s\right) \operatorname{F}\left(s\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_product_off_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Luis Báez-Duarte (2003). *A new necessary and sufficient condition for the Riemann hypothesis*. URL: <https://arxiv.org/abs/math/0307215v1>.

*Commentary.*

For every s in H distinct from one, raw riemannZeta(s)*F(s)=1. This follows from the regularized product and directly supplies the zero-exclusion step used for RH. The pole exception is essential.

## References

- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_complex_finite_sum`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_decay_implies_rh`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_epsilon_half_iff`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_at_one`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_differentiable`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_locally_uniform`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_product_off_one`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_off_one`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_reciprocal_uniform`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_regularized_product`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_summable`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_newton_uniform`
- Truth anchor: `D5/S3/Weil/Analytic/BaezDuarteContinuation.baez_duarte_original_decay_implies_rh`
- Dependency: [D5/S3/Analytic/SeriesInequalities/BaezDuarteNewtonMajorant](../../Analytic/SeriesInequalities/BaezDuarteNewtonMajorant.md)
- Dependency: [D5/S3/Weil/Analytic/BaezDuarteNewton](BaezDuarteNewton.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../ZetaBridge/RightHalfStripRiemannReduction.md)
