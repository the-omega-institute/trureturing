# Original H6 pays the actual critical exponential B domain

## Abstract

Original H6 pays the actual critical exponential B domain

The original F is preserved through fullTheta, actualGammaProfile and actualSuzukiEvenBProfile. The physical H6 budget alone supplies this exponential domain. It supplies neither the logarithmic Fourier budget nor the nonpositive complete-energy hypothesis used separately in W366. No RH, Robin inequality, density, or global Riemannian completeness conclusion is asserted.

**Theorem 1.1 (Increasing weights raise the future-tail decay rate).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.right_exponential_tail_exponential_conjugation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.right_exponential_tail_exponential_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the actual integral, exp(a t) R_k u(t)=R_(k+a)(exp(a .)u)(t). The rate is k+a. In the critical Suzuki application k=a=5/4, so the weighted tail has rate 5/2.

**Theorem 1.2 (The same actual Gamma profile has its critical weighted domain).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_gamma_profile_critical_exponential_l2_and_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_gamma_profile_critical_exponential_l2_and_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the original physical H6 source F, exp(5t/4) actualGammaProfile(F,t) is in L2 on t>0. Its squared mass is exactly pi^(-5/2) times integral_(x>pi) x^6 |fullTheta(F,x)|^2. This is a half-line input to B, and its identity keeps the complete theta transform of this same F.

**Theorem 1.3 (The actual even-B profile has both L2 domains and an original-source budget).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_suzuki_even_b_l1_l2_critical_exponential`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_suzuki_even_b_l1_l2_critical_exponential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same original H6 source F, its actual full-line even-B profile is in L1 and L2, and exp(5|r|/2) times that profile is in L2. The last squared mass is at most (68/25) pi^(7/2) (sum_(n>=1) n^(-3))^2 times integral_(x>pi) (x/pi)^6 |F(x)|^2. The nonoptimal factor 68/25 comes from 2|v|^2+(9/2)|R_(5/2)v|^2 and the global tail L2 bound. The existing private total sixth-moment theta norm estimate is consumed directly. Under t=2|r|, the two real half-lines cancel the Jacobian; no extra factor 2 occurs.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_gamma_profile_critical_exponential_l2_and_mass`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.actual_h6_suzuki_even_b_l1_l2_critical_exponential`
- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiExponentialL2.right_exponential_tail_exponential_conjugation`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge](ActualSuzukiMeanCharge.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailGlobalL2](RightExponentialTailGlobalL2.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/RightExponentialTailL2](RightExponentialTailL2.md)
