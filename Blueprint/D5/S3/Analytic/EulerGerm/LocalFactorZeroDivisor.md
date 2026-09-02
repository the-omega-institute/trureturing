# Golden Germ Local-Factor Zero Divisor

## Abstract

The normalized golden germ correction product has exactly the union of its local zero sets, while each local factor is analytic on the positive half-plane and a strict boundary norm gap gives a zero certificate.

**Theorem 1.1 (The normalized product vanishes exactly at a local-factor zero).**

$$\forall s \in \mathbb{C},\; \frac{1}{\varphi^{4}} < \Re(s) \Rightarrow \left(\prod_{p\in \operatorname{Primes}\left(\mathbb{N}\right)}(1 - p^{-s \times \varphi^{3}}) \times (1 + p^{-s \times \varphi^{2}})^{-1} \times \operatorname{germLocalFactor}\left(s, p\right) = 0 \Leftrightarrow \left(\exists p \in \operatorname{Primes}\left(\mathbb{N}\right),\; \operatorname{germLocalFactor}\left(s, p\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.G3_eq_zero_iff_exists_local_factor_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized factor is the literal correction factor in the frozen second-order factorization. Its two elementary multipliers are nonzero on the stated half-plane, and the frozen summable deviation makes the infinite product nonzero whenever every local factor is nonzero.

This equivalence does not assert that any local factor vanishes. The numerical evidence for prime-two zeros in the target window remains recorded in the theory volume.

**Theorem 1.2 (Every prime-local factor is analytic when the real part is positive).**

$$\forall p \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \operatorname{AnalyticOnNhd}\left(\mathbb{C}, (s\in \mathbb{C} \mapsto \operatorname{germLocalFactor}\left(s, p\right)), \left\{0 < \Re(s) \mid s \in \mathbb{C}\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.germLocalFactor_analyticOnNhd_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local series is normally summable on every smaller positive half-plane. Pinned Mathlib's locally uniform series theorem therefore supplies complex differentiability and analyticity.

Analyticity does not assert a local-factor zero. The numerical prime-two evidence remains in the theory volume.

**Theorem 1.3 (A strict boundary norm gap forces an interior zero).**

$$\forall f \in \mathbb{C} \to \mathbb{C}, c \in \mathbb{C}, r \in \mathbb{R},\; \left(0 < r \land \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, f, \operatorname{closedBall}\left(c, r\right)\right) \land \left(\forall z \in \mathbb{C},\; z \in \operatorname{sphere}\left(c, r\right) \Rightarrow \left\lVert f\left(c\right) \right\rVert < \left\lVert f\left(z\right) \right\rVert\right)\right)\right) \Rightarrow \left(\exists z \in \mathbb{C},\; z \in \operatorname{ball}\left(c, r\right) \land f\left(z\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.exists_zero_in_ball_of_boundary_norm_gt_center` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the function had no zero in the closed ball, its reciprocal would be analytic there. The maximum-modulus theorem for the reciprocal would then contradict the strict boundary gap.

The criterion does not establish the numerical gap for a golden local factor and therefore asserts no local-factor zero.

## References

- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.G3_eq_zero_iff_exists_local_factor_zero`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.exists_zero_in_ball_of_boundary_norm_gt_center`
- Truth anchor: `D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor.germLocalFactor_analyticOnNhd_pos`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermSecondOrderFactorization](GoldenGermSecondOrderFactorization.md)
