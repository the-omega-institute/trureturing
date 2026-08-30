# Target Visibility and Minimum Variance

## Abstract

Exact target visibility gives the minimum-variance isotropic-noise estimator.

**Theorem 1.1 (The visible target coefficient minimizes isotropic-noise variance).**

$$\begin{gathered}\forall K, S, O: Type,\\{}RCLike(K) \land NormedAddCommGroup(S) \land InnerProductSpace(K, S) \land\\{}FiniteDimensional(K, S) \land NormedAddCommGroup(O) \land InnerProductSpace(K, O) \land\\{}FiniteDimensional(K, O) \Rightarrow\\{}M: S \to O, v\in S,\\{}(\forall x, y, M(x) = M(y) \Rightarrow \langle v, x \rangle = \langle v, y \rangle) \land (C = \Sigma^{2} I) \Rightarrow\\{}\exists s\in S, a\in O,\\{}M^{*}(a) = v \land (\forall b, M^{*}(b) = v \Rightarrow Var(C, a) \leq Var(C, b)) \land Var(C, a) = \Sigma^{2} \langle v, s \rangle.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.target_visibility_minimum_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a linear measurement between finite-dimensional real or complex inner-product spaces, exact target visibility supplies the unique minimum-norm unbiased coefficient from the condition-cost theorem.

If the observation covariance is sigma squared times the identity, the variance of every coefficient is sigma squared times its squared norm. The minimum-norm coefficient therefore also has minimum variance, including when sigma is zero.

Its variance is sigma squared times the target inner product with the canonical visible Gram preimage, recovering the second conclusion of Theorem 214.2 from the existing first conclusion.

**Theorem 1.2 (Target visibility is necessary).**

$$\neg (\forall x, y, 0: \mathbb{R} \to \mathbb{R}(x) = 0: \mathbb{R} \to \mathbb{R}(y) \Rightarrow \langle 1, x \rangle = \langle 1, y \rangle) \land IsIsotropicCovariance(0: \mathbb{R} \to \mathbb{R}, 0) \land \neg\exists q\in \mathbb{R} \times \mathbb{R}, MinimumVarianceCertificate(0: \mathbb{R} \to \mathbb{R}, 1, 0, 0, q).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.target_visibility_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the zero real measurement and the nonzero target one, every adjoint coefficient is zero. Hence no unbiased coefficient exists and no minimum-variance certificate can be formed.

**Theorem 1.3 (Isotropic covariance is necessary).**

$$\begin{gathered}\forall x, y, span((1, 0))(x) = span((1, 0))(y) \Rightarrow \langle 1, x \rangle = \langle 1, y \rangle \land\\{}\neg IsIsotropicCovariance(rankOne((1, 1), (1, 1)), 1) \land\\{}\neg MinimumVarianceCertificate(span((1, 0)), 1, rankOne((1, 1), (1, 1)), 1, (1, (1, 0))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.isotropic_covariance_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A concrete two-coordinate real example uses measurement direction (1,0) and rank-one covariance in direction (1,1). The canonical coefficient (1,0) has positive variance, while the unbiased competitor (1,-1) has zero variance.

Thus minimum Euclidean norm need not imply minimum variance once the covariance is not isotropic.

**Theorem 1.4 (Degenerate inputs still have certificates).**

$$(\exists q\in \mathbb{R} \times \mathbb{R}, MinimumVarianceCertificate(0, 0, 0, 0, q)) \land (\exists q\in EuclideanSpace(\mathbb{R}, Fin(0)) \times EuclideanSpace(\mathbb{R}, Fin(0)), MinimumVarianceCertificate(I, 0, 0, 0, q)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.degenerate_inputs_have_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero target and zero noise scale, the zero real measurement has a certificate. The identity measurement on the singleton zero-dimensional Euclidean space has one as well.

These witnesses audit constant zero measurement, identity measurement, zero covariance, zero scale, and the Fin 0 index case. An empty carrier is impossible for a normed additive group because it contains zero.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.degenerate_inputs_have_witnesses`
- Truth anchor: `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.isotropic_covariance_is_necessary`
- Truth anchor: `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.target_visibility_is_necessary`
- Truth anchor: `D5/S3/Observer/Conditioning/TargetVisibilityMinimumVariance.target_visibility_minimum_variance`
- Dependency: [D5/S3/Observer/Conditioning/TargetVisibilityConditionCost](TargetVisibilityConditionCost.md)
