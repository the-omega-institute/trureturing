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

For the fixed complex center c defined above, put r = c.re = 23815329946211908/10^17, phi = (1 + sqrt(5))/2, L = 1/(2*phi^3) and U = 1/phi^2. For every p : Nat.Primes define goldenCandidateOrbitScale(p) = log(2)/log(p) and goldenCandidateOrbit(p) = goldenCandidateOrbitScale(p)*r. Here log is the real natural logarithm and p is coerced to its positive real value. These expressions use this exact c; they introduce no zero assumption. The logarithmic parameter correspondence is the one in `D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling`: with the prime-two input s and prime-p output (log(2)/log(p))*s, the local-factor values agree. Since the scale is real, its product with c has real part goldenCandidateOrbit(p).

The complete prime classification is: for every p : Nat.Primes, L < goldenCandidateOrbit(p) and goldenCandidateOrbit(p) < U if and only if p.val = 2 or p.val = 3. There is no upper bound on p. More precisely, L < goldenCandidateOrbit(3) < U, while goldenCandidateOrbit(5) < L; indeed goldenCandidateOrbit(p) < L for every prime p with 5 <= p.val. The arguments 2, 3 and 5 denote their prime-subtype values.

The algebraic estimates use sqrt(5)^2 = 5 and sqrt(5) >= 0 to obtain 1618/1000 < phi < 13/8. The identity phi^2 = phi + 1 gives phi^3 = 2*phi + 1, hence 2*(1618/1000) + 1 < phi^3 < 17/4. The fixed rational coordinate satisfies 238/1000 < r < 1/4 and r > 0. Thus, writing A = 2*phi^3*r, the lower comparison 2*(2*(1618/1000) + 1)*(238/1000) > 2 yields A > 2. For the upper comparison, phi^3*r < (17/4)*r < 17/16, so A < 17/8 < 9/4. Therefore 2 < A < 9/4.

All logarithmic denominators are positive because every prime is greater than one. Strict logarithm monotonicity and log(x^n) = n*log(x) give log(3) < log(4) = 2*log(2). The exact integer inequality 2^9 = 512 < 625 = 5^4 gives 9*log(2) < 4*log(5), hence (9/4)*log(2) < log(5). These comparisons require only positive real inputs.

For p = 3, log(2) < log(3), so 0 < log(2)/log(3) < 1 and goldenCandidateOrbit(3) < r < U, using c_in_golden_window. Also log(3) < 2*log(2) < A*log(2). Dividing by the positive log(3) yields 1 < (log(2)/log(3))*A = (2*phi^3)*goldenCandidateOrbit(3), which is exactly L < goldenCandidateOrbit(3). For any prime p >= 5, log(p) >= log(5) > (9/4)*log(2) > A*log(2). Dividing by the positive log(p) yields (2*phi^3)*goldenCandidateOrbit(p) < 1, or goldenCandidateOrbit(p) < L. This includes p = 5 and excludes the whole unbounded range uniformly.

For p = 2, log(2)/log(2) = 1, so goldenCandidateOrbit(2) = r and c_in_golden_window supplies both strict bounds. Every prime has p.val >= 2, and 4 is composite. Thus a prime distinct from 2 and 3 has p.val >= 5 and is excluded by the preceding uniform estimate; conversely primes 2 and 3 satisfy both bounds. This proves both directions of the classification using the fixed center, logarithm monotonicity, the golden-ratio identities and the stated rational comparisons.

This is an arithmetic application of the existing center and scaling results. The center-window statement and the parameter correspondence do not assert that c is a local-factor zero, that a transported candidate is a zero, or that the center-jet hypotheses hold. The classification gives no RH conclusion and no necessary or optimal summability criterion.

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
- Narrative reference: [D5/S3/Analytic/EulerGerm/LocalFactorUniversalScaling](../EulerGerm/LocalFactorUniversalScaling.md)
