# Golden Germ Zero Certificate: Curvature and First-Mode Jet

## Abstract

This is layer L2a of the G-c certificate in 增订三十四: it unconditionally discharges the third center-jet hypothesis of germ_zero_of_center_jet by proving curvature at most 400 throughout Q, certifies log 2 to 2^{-60}, and proves the v <= 1 prefix of the derivative real-part bound.

**Definition 1.1 (The rational 60-term approximation to log 2).**

$$logTwoApprox = \sum_{i=0}^{59}\frac{{\frac{1}{2}}^{i + 1}}{i + 1}$$

*Formalization.* `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.logTwoApprox` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named rational constant is the first sixty terms of the binary logarithm series.

**Theorem 1.2 (The explicit 60-term series certifies log 2 to 2^{-60}).**

$$\left|\operatorname{log}\left(2\right) - \sum_{i=0}^{59}\frac{{\frac{1}{2}}^{i + 1}}{i + 1}\right| \le {\frac{1}{2}}^{60}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.log_two_binary_60_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pinned geometric-series remainder theorem gives the error bound for the displayed real series.

**Theorem 1.3 (The rational approximation certifies log 2 to 2^{-60}).**

$$\left|\operatorname{log}\left(2\right) - logTwoApprox\right| \le \frac{1}{2^{60}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.log_two_binary_60` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric-series remainder bounds the error of logTwoApprox by one part in 2^{60}.

**Theorem 1.4 (The first nonconstant mode has derivative real part greater than one).**

$$1 < \Re{\operatorname{deriv}\left(\operatorname{g}\left(1\right), c\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g1_deriv_re_gt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A certified reduction of the mode-one phase modulo 3 pi, together with explicit cosine and decay bounds, proves the v <= 1 prefix.

**Theorem 1.5 (The 61-mode curvature is at most 118 on Q).**

$$\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{g}\left(60\right)\right), s\right) \right\rVert \le 118$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g60_curvature_le_118` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mode-wise second-derivative identity and a rational geometric majorant give the uniform bound 118.

**Theorem 1.6 (The layer-1 curvature hypothesis holds on Q).**

$$\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{g}\left(60\right)\right), s\right) \right\rVert \le 400$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g60_curvature_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharper bound 118 implies the required bound 400, discharging the third center-jet hypothesis of germ_zero_of_center_jet unconditionally on Q. The full inequalities 187/100 < Re(g_60'(c)) and ||g_60(c)|| < 4*10^{-10} belong to L2c and are not claimed here. This module makes no claim about RH.

## References

- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g1_deriv_re_gt_one`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g60_curvature_le`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.g60_curvature_le_118`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.logTwoApprox`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.log_two_binary_60`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateJet.log_two_binary_60_sum`
- Dependency: [D5/S3/Analytic/GermWindow/GermZeroCertificateReduction](GermZeroCertificateReduction.md)
