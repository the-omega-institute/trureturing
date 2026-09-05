# Golden Germ Zero Certificate Reduction

## Abstract

The first layer of the golden G-c certificate turns three finite center-jet inequalities into a prime-two local-factor zero inside the candidate window.

**Definition 1.1 (Candidate center).**

$$c = \langle\frac{23815329946211908}{10^{17}}, \frac{5256712292901926}{10^{15}}\rangle$$

*Formalization.* `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complex center is the frozen numerical candidate used by the G-c certificate.

**Definition 1.2 (Candidate half-width).**

$$h = \frac{1}{2 \cdot 10^{8}}$$

*Formalization.* `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.h` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-width is five times ten to the minus ninth.

**Definition 1.3 (Candidate square).**

$$Q = \operatorname{Rectangle}\left(c - h - h \cdot i, c + h + h \cdot i\right)$$

*Formalization.* `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The axis-parallel square has center c and coordinate half-width h.

**Definition 1.4 (Finite local truncation).**

$$\operatorname{g}\left(V, s\right) = \sum_{v=0}^{V}2^{-s \cdot \operatorname{o5Beta}\left(v\right)}$$

*Formalization.* `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.g` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The function g(V,s) is the first V+1 terms of the p = 2 golden local factor.

**Theorem 1.5 (The candidate square lies in the target ball).**

$$Q \subseteq \operatorname{ball}\left(c, \frac{1}{10^{8}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q_subset_ball` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate control puts every point of Q strictly within distance 10^{-8} of c.

**Theorem 1.6 (The candidate square stays in the analytic half-plane).**

$$Q \subseteq \left\{0 < \Re{s} \mid s \in \mathbb{C}\right\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q_subset_re_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point of Q has positive real part, so the frozen local analyticity theorem applies.

**Theorem 1.7 (The center lies in the golden window).**

$$\frac{1}{2 \cdot \varphi^{3}} < \Re{c} \land \Re{c} < \frac{1}{\varphi^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c_in_golden_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real coordinate of c lies strictly between the two displayed golden thresholds.

**Theorem 1.8 (The square contains its center).**

$$c \in Q$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c_mem_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The candidate square is inhabited by c.

**Theorem 1.9 (The local factor splits into a finite head and shifted tail).**

$$\forall s \in \mathbb{C}, N \in \mathbb{N},\; 0 < \Re{s} \Rightarrow \operatorname{germLocalFactor}\left(s, 2\right) = \sum_{v=0}^{N-1}2^{-s \cdot \operatorname{o5Beta}\left(v\right)} + \sum_{k=0}^{\infty}2^{-s \cdot \operatorname{o5Beta}\left(k + N\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_eq_trunc_add_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute summability on the positive half-plane justifies the exact head-tail identity.

**Theorem 1.10 (The prime-two local tail obeys an explicit geometric bound).**

$$\forall sigma \in \mathbb{R}, s \in \mathbb{C}, V \in \mathbb{N},\; \left(0 < sigma \land sigma \le \Re{s}\right) \Rightarrow \left\lVert \operatorname{germLocalFactor}\left(s, 2\right) - \sum_{v=0}^{V}2^{-s \cdot \operatorname{o5Beta}\left(v\right)} \right\rVert \le \frac{2^{-sigma \cdot \left(\sqrt{5} \cdot \left(V + 1\right) + \frac{1}{\varphi} - 1\right)}}{1 - 2^{-sigma \cdot \sqrt{5}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_two_tail_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen lower growth bound for o5Beta majorizes the shifted tail by a geometric series with the displayed exponent and denominator.

**Theorem 1.11 (The 61-term tail is below 5.8 times 10 to the minus ten).**

$$\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{germLocalFactor}\left(s, 2\right) - \operatorname{g}\left(60, s\right) \right\rVert < \frac{58}{10^{11}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_two_tail_Q_V60` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit logarithm and exponential inequalities specialize the geometric estimate uniformly on Q.

**Theorem 1.12 (A unique simple comparison zero transfers existence).**

$$\forall f \in \mathbb{C} \to \mathbb{C}, a \in \mathbb{C} \to \mathbb{C}, z \in \mathbb{C}, w \in \mathbb{C}, r \in \mathbb{C},\; \left(\Re{z} < \Re{w} \land \left(\operatorname{Im}\left(z\right) < \operatorname{Im}\left(w\right) \land \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, f, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\operatorname{AnalyticOnNhd}\left(\mathbb{C}, a, \operatorname{Rectangle}\left(z, w\right)\right) \land \left(\left(\forall s \in \mathbb{C},\; s \in \operatorname{RectangleBorder}\left(z, w\right) \Rightarrow \left\lVert f\left(s\right) - a\left(s\right) \right\rVert < \left\lVert a\left(s\right) \right\rVert\right) \land \left(r \in \operatorname{Rectangle}\left(z, w\right) \land \left(\left(\forall s \in \mathbb{C},\; s \in \operatorname{Rectangle}\left(z, w\right) \Rightarrow \left(a\left(s\right) = 0 \Leftrightarrow s = r\right)\right) \land \operatorname{analyticOrderNatAt}\left(a, r\right) = 1\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\exists s \in \mathbb{C},\; s \in \operatorname{Rectangle}\left(z, w\right) \land f\left(s\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.rouche_exists_zero_rectangle_of_unique_simple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rectangle Rouché theorem is another driver's frozen node, bound here by the name rectangle_zero_count_eq_of_norm_sub_lt; equal multiplicity counts force the target zero set to be nonempty.

**Theorem 1.13 (Curvature controls the truncation remainder).**

$$\left(\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{g}\left(60\right)\right), s\right) \right\rVert \le 400\right) \Rightarrow \left(\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{g}\left(60, s\right) - \left(\operatorname{g}\left(60, c\right) + \operatorname{deriv}\left(\operatorname{g}\left(60\right), c\right) \cdot \left(s - c\right)\right) \right\rVert \le \frac{4}{10^{14}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.truncation_taylor_remainder_of_curv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform second-derivative bound on Q gives the displayed affine Taylor remainder bound for the 61-term truncation.

**Theorem 1.14 (Three center-jet inequalities imply a nearby local-factor zero).**

$$\left(\left\lVert \operatorname{g}\left(60, c\right) \right\rVert < \frac{4}{10^{10}} \land \left(\frac{187}{100} < \Re{\operatorname{deriv}\left(\operatorname{g}\left(60\right), c\right)} \land \left(\forall s \in \mathbb{C},\; s \in Q \Rightarrow \left\lVert \operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{g}\left(60\right)\right), s\right) \right\rVert \le 400\right)\right)\right) \Rightarrow \left(\exists z \in \mathbb{C},\; z \in \operatorname{ball}\left(c, \frac{1}{10^{8}}\right) \land \operatorname{germLocalFactor}\left(z, 2\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germ_zero_of_center_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the first layer of the G-c certificate in 增订十/三十三: it reduces the candidate zero of the p = 2 golden local factor to three finite numerical inequalities about the 61-term truncation at the center. The convention is β(1) = φ², correcting the panel brief. This theorem does not claim that the three jet inequalities hold; proving them is layer 2, so this module makes no unconditional claim that a zero exists yet. It makes no claim about RH.

## References

- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q_subset_ball`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.Q_subset_re_pos`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c_in_golden_window`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.c_mem_Q`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.g`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_eq_trunc_add_tail`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_two_tail_Q_V60`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germLocalFactor_two_tail_le`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.germ_zero_of_center_jet`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.h`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.rouche_exists_zero_rectangle_of_unique_simple`
- Truth anchor: `D5/S3/Analytic/GermWindow/GermZeroCertificateReduction.truncation_taylor_remainder_of_curv`
- Dependency: [D5/S3/Analytic/EulerGerm/LocalFactorZeroDivisor](../EulerGerm/LocalFactorZeroDivisor.md)
- Dependency: [D5/S3/Weil/ZetaAnalytic/RoucheZeroCount](../../Weil/ZetaAnalytic/RoucheZeroCount.md)
