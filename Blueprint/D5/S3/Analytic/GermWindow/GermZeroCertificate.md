# Generated Golden Germ Zero Certificate

## Abstract

The generated L2c certificate encloses all sixty-one modes at the frozen candidate, assembles the center norm and derivative margins, and closes the prime-two golden local-factor zero obligation.

The in-repo generator tools/scripts/agent/germ_jet_certificate.py emits this module deterministically; --check regenerates and byte-compares it. Its 61-row rational table has columns termReLo/Hi, termImLo/Hi, derivReLo/Hi, and derivImLo/Hi for v = 0,...,60. Exact assembly gives center real interval [-6.898169e-12,-6.8981e-12], center imaginary interval [2.75425869e-10,2.75425943e-10], additive norm bound 17645257/62500000000000000 = 2.82324112e-10, and derivative-real lower bound 1877338029556539187/10^18 = 1.877338029556539187.

**Theorem 1.1 (The 61-mode truncation is smaller than four times 10^{-10}).**

$$\left\lVert \operatorname{g}\left(60, c\right) \right\rVert < \frac{4}{10^{10}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificate.g60_center_norm_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real and imaginary generated interval sums are converted by the frozen coordinate norm lemma. The certified 2.82324112e-10 bound lands below the preregistered 2.9e-10 falsifier threshold.

**Theorem 1.2 (The derivative real part exceeds 1.87).**

$$\frac{187}{100} < \Re{\operatorname{deriv}\left(\operatorname{g}\left(60\right), c\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificate.g60_center_deriv_re_gt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the sixty-one exact derivative lower endpoints gives 1.877338029556539187, so the required strict 187/100 margin holds.

**Theorem 1.3 (The prime-two golden local factor has a nearby zero).**

$$\exists z \in \mathbb{C},\; z \in \operatorname{ball}\left(c, \frac{1}{10^{8}}\right) \land \operatorname{germLocalFactor}\left(z, 2\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificate.germLocalFactor_two_has_zero_near_candidate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This bind-only closure combines the generated center norm and derivative bounds with the frozen L2a curvature theorem and the L1 center-jet reduction. It closes G-c: the p = 2 golden local factor has a zero within 10^{-8} of c approximately 0.23815 + 5.25671 i. This is the kernel refutation of addendum ten's claim of no cancellation in the window. It says nothing about RH itself.

## References

- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificate.g60_center_deriv_re_gt`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificate.g60_center_norm_lt`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificate.germLocalFactor_two_has_zero_near_candidate`
- Dependency: [D5/S3/Analytic/Certified/TrigEnvelopePhaseReduction](../Certified/TrigEnvelopePhaseReduction.md)
- Dependency: [D5/S3/Analytic/GermWindow/GermJetModeLemma](GermJetModeLemma.md)
- Dependency: [D5/S3/Analytic/GermWindow/GermZeroCertificateJet](GermZeroCertificateJet.md)
- Dependency: [D5/S3/Analytic/GermWindow/GermZeroCertificateReduction](GermZeroCertificateReduction.md)
