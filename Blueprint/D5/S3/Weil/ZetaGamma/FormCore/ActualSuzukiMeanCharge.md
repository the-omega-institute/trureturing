# The original actual Suzuki mean

## Abstract

The original actual Suzuki mean

Here mu(F) is the integral over the full real line of actualSuzukiEvenBProfile(F), exactly the original H6 mean constraint. It is distinct from the positive-half-line Gaussian central Mellin charge used by the weighted coefficient core. These are source-relative analytic consequences of the existing original physical domain and complete-theta constructions, with no RH-resolution or literature-priority claim.

An application of the existing exponential-moment, translation, H6 theta-summability and dominated-convergence results gives a concrete source with nonzero original mean. For every real p>=2, E_p(x)=exp(-p x) is original H6, mu(E_p) has zero imaginary part and its real part is strictly positive.

To see the sign, put U=fullTheta(E_p), M0=integral_(x>pi) Re(U(x)) and M5=integral_(x>pi) x^(5/4) Re(U(x)). Every physical mode is n^4 exp(-p n^2 x), n>=1. H6 supplies the actual L1 domains and almost-everywhere summability, so dominated convergence exchanges the complete positive mode series with its zeroth and second moment integrals. The first mode makes M0>0. The rate q=p n^2 is at least 2, and the exact exponential moments give M2<=(pi^2+pi+1/2) M0. Since x^(5/4)<=x^2 for x>pi, M5<=M2. The original mean formula then gives Re(mu(E_p))=(6 pi^(5/4) M0-M5)/5>0, because pi^2+pi+1/2<6 pi^(5/4). All these moments are genuine integrals of the same complete theta source.

The positive original mean provides a nonzero direction for source corrections. Original Gamma Fourier form-domain membership for this exponential source and density of a corrected Gaussian core remain separate obligations. The H6 conditions of the source-linearity interface below must still be paid when forming a correction.

**Theorem 1.1 (The actual original mean has a bounded kernel).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original H6 source F, the full-line even-B profile is genuinely integrable. Its original mean mu(F) equals the positive-half-line integral of K(t) actualGammaProfile(F,t), with K(t)=(6 exp(-5t/4)-1)/5. The even doubling formula, genuine L1 tail mass and Bochner integral algebra retain the endpoint contribution.

**Theorem 1.2 (The original mean has an L1 bound).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The kernel lies between -1/5 and 1 on the positive half-line. Consequently the norm of the original mean is at most the L1 norm of the same actual complete-theta profile; no coefficient-charge reinterpretation enters.

**Theorem 1.3 (A real actual profile gives a real original mean).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An almost-everywhere real actual complete-theta profile gives a real original mean. The original H6 hypothesis supplies the true integral domain; this theorem does not assume pointwise real behavior at the boundary.

**Theorem 1.4 (The original mean respects actual profile relations).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three original H6 sources whose actual complete-theta profiles satisfy the stated almost-everywhere complex linear relation, the original means satisfy that relation. This conditional interface retains its profile hypothesis.

**Theorem 1.5 (The original mean is linear on actual H6 source combinations).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex a,b and original H6 sources F,G such that H(x)=a F(x)+b G(x) is also original H6, mu(H)=a mu(F)+b mu(G). There is no additional assumption about the profiles. The proof uses the existing almost-everywhere summability of the literal physical-mode series, derives actual fullTheta linearity, and transports it through the genuine physical moments of orders 0 and 5/4. It then reconstructs the original full-line even-B mean from those moments. No stronger endpoint convergence or Gamma Fourier form-domain is inferred.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanZeroTrace](ActualSuzukiMeanZeroTrace.md)
