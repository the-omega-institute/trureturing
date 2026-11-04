# The signed Mills-ratio remainders

## Abstract

Positive Laplace kernels for the signed Xu–Yang Mills-ratio remainders.

**Definition 1.1 (CompletelyMonotoneOn).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \operatorname {CompletelyMonotoneOn}\left(f\right) = \left(\left(\operatorname {ContDiffOn}\left(\mathbb {R}, \infty, f, \operatorname {Set.Ioi}\left(0\right)\right)\right) \land \left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(0 \le \left(-1\right)^{m} \cdot \operatorname {iteratedDeriv}\left(m, f, x\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.CompletelyMonotoneOn` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

The definition is C-infinity on the positive half-line together with the sign of every ordinary iterated derivative, exactly the complete-monotonicity condition.

**Definition 1.2 (millsRatio).**

$$\forall x \in \mathbb {R},\; \operatorname {millsRatio}\left(x\right) = \operatorname {Real.exp}\left(\frac{\left(x\right)^{2}}{2}\right) \cdot \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(x\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\frac{\left(t\right)^{2}}{2}\right)\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.millsRatio` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

The Gaussian-tail normalization is R in the source, printed page 2. Extending the defining expression to every real x does not change its positive-domain values.

**Definition 1.3 (Y).**

$$\forall a \in \mathbb {R},\; \forall b \in \mathbb {R},\; \forall x \in \mathbb {R},\; \operatorname {Y}\left(a, b, x\right) = \left(\left(x\right)^{2} + a\right) \cdot \left(\operatorname {millsRatio}\left(x\right)\right)^{2} + b \cdot x \cdot \operatorname {millsRatio}\left(x\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.Y` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

Equation (1.8), printed page 3, with its surrounding statement: “Note that all bounds of the form ϕ_{p,q,r}(x) can be derived from the inequality Y_{a,b}(x) := (x² + a)R²(x) + bxR(x) < (>) c for all x > 0, a, b ∈ ℝ, where c = lim_{x→0} Y_{a,b}(x) = aπ/2 or c = lim_{x→∞} Y_{a,b}(x) = b + 1.” Y is the displayed defining expression.

**Definition 1.4 (u).**

$$\forall k \in \mathbb {N},\; \forall a \in \mathbb {R},\; \forall b \in \mathbb {R},\; \operatorname {u}\left(k, a, b\right) = \frac{\left(b + 1\right) \cdot \left(2\right)^{k} \cdot \operatorname {Real.Gamma}\left(k + \frac{1}{2}\right)}{\operatorname {Real.Gamma}\left(\frac{1}{2}\right)} + \left(k - a\right) \cdot \operatorname {Nat.factorial}\left(\operatorname {Nat.sub}\left(k, 1\right)\right) \cdot \sum_{j \in \operatorname {Finset.range}\left(k\right)} \left(\frac{\left(2\right)^{j} \cdot \operatorname {Real.Gamma}\left(j + \frac{1}{2}\right)}{\operatorname {Real.Gamma}\left(\frac{1}{2}\right) \cdot \operatorname {Nat.factorial}\left(j\right)}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.u` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

Equation (3.7), printed page 6: “where u_n ≡ u_n(a, b) = (b + 1) 2^n Γ(n + 1/2)/Γ(1/2) + (n − a)(n − 1)! Σ_{k=0}^{n−1} 2^k Γ(k + 1/2)/(Γ(1/2) k!). In particular, u₁ = b + 2 − a, u₂ = 3b + 7 − 2a, u₃ = 15b + 36 − 7a, and u₄ = 105b − 36a + 249.” Natural indices in real arithmetic are coerced to real numbers; the Gamma factors remain in their original form. The factorial index Nat.sub(k,1) is natural subtraction, truncated at zero. It agrees with k-1 for every positive coefficient index used in the source.

**Definition 1.5 (D).**

$$\forall n \in \mathbb {N},\; \forall x \in \mathbb {R},\; \forall a \in \mathbb {R},\; \operatorname {D}\left(n, x, a\right) = \operatorname {Y}\left(a, a - 2, x\right) - \left(a - 1 + \sum_{k \in \operatorname {Finset.Icc}\left(1, n\right)} \left(\frac{\left(-1\right)^{k} \cdot \operatorname {u}\left(k, a, a - 2\right)}{\left(x\right)^{2 \cdot k}}\right)\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.D` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

This is the finite asymptotic remainder appearing in Conjecture 7.1.

**Definition 1.6 (The complete-monotonicity assertion for every n at least two).**

$$claim = \left(\forall n \in \mathbb {N},\; \left(2 \le n\right) \Rightarrow \left(\operatorname {CompletelyMonotoneOn}\left(x: \mathbb {R}\mapsto \left(-1\right)^{n} \cdot \operatorname {D}\left(n, x, -1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.claim` (`✓ std3`).

*Citation.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

Equation (1.8), printed page 3, complete defining statement: “Note that all bounds of the form ϕ_{p,q,r}(x) can be derived from the inequality Y_{a,b}(x) := (x² + a)R²(x) + bxR(x) < (>) c for all x > 0, a, b ∈ ℝ, where c = lim_{x→0} Y_{a,b}(x) = aπ/2 or c = lim_{x→∞} Y_{a,b}(x) = b + 1.”

Equation (3.7), printed page 6, complete defining statement: “where u_n ≡ u_n(a, b) = (b + 1) 2^n Γ(n + 1/2)/Γ(1/2) + (n – a)(n – 1)! Σ_{k=0}^{n–1} 2^k Γ(k + 1/2)/(Γ(1/2) k!). In particular, u₁ = b + 2 – a, u₂ = 3b + 7 – 2a, u₃ = 15b + 36 – 7a, and u₄ = 105b – 36a + 249.”

Conjecture 7.1, printed page 27, complete statement with line breaks joined: “Moreover, inspired by Theorem 4.2, we propose the following conjecture. Conjecture 7.1 Let D_n(x, a) = Y_{a,a–2}(x) – (a – 1 + Σ_{k=1}^{n} (–1)^k u_k / x^{2k}), where u_k is defined by (3.7). Then x ↦ (–1)^n D_n(x, –1) is CM on (0, ∞).”

The lower index is n≥2. The source coefficients at a=-1, b=-3 vanish at indices one and two, so D1 equals D2 and the signed index-one remainder is -D2. The definition uses C-infinity and the paper’s condition (-1)^m f^(m)≥0 for every natural m, including zero.

**Theorem 1.7 (millsLaplace).**

$$\forall x \in \mathbb {R},\; \operatorname {millsRatio}\left(x\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right) - \frac{\left(t\right)^{2}}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.millsLaplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation by x in the Gaussian tail gives the positive-ray Laplace representation.

**Theorem 1.8 (millsLaplaceIntegrable).**

$$\forall x \in \mathbb {R},\; \left(0 \le x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right) - \frac{\left(t\right)^{2}}{2}\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.millsLaplaceIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative x the tilted Gaussian is dominated by the integrable Gaussian.

**Theorem 1.9 (millsSquareConvolution).**

$$\forall x \in \mathbb {R},\; \left(0 \le x\right) \Rightarrow \left(\left(\operatorname {millsRatio}\left(x\right)\right)^{2} = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {intervalIntegral}\left(s: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\frac{\left(s\right)^{2}}{2}\right) \cdot \operatorname {Real.exp}\left(-\frac{\left(t - s\right)^{2}}{2}\right), 0, t, \operatorname {volume}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.millsSquareConvolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive-ray convolution integral equals the product of the two Mills Laplace integrals.

**Theorem 1.10 (convolutionClosed).**

$$\forall t \in \mathbb {R},\; \operatorname {intervalIntegral}\left(s: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\frac{\left(s\right)^{2}}{2}\right) \cdot \operatorname {Real.exp}\left(-\frac{\left(t - s\right)^{2}}{2}\right), 0, t, \operatorname {volume}\right) = t \cdot \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \operatorname {Real.exp}\left(\frac{-\left(\left(1 + \left(v\right)^{2}\right) \cdot \left(t\right)^{2}\right)}{4}\right), 0, 1, \operatorname {volume}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.convolutionClosed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An affine substitution and evenness of the Gaussian give the closed convolution kernel.

**Definition 1.11 (moment).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \operatorname {moment}\left(f, m, x\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \left(-t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right)\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed Laplace moments give the derivatives of the zeroth moment.

**Theorem 1.12 (momentDeriv).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(f\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb {R},\; \left(0 < t\right) \Rightarrow \left(0 \le \operatorname {f}\left(t\right)\right)\right) \Rightarrow \left(\left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)\right) \Rightarrow \left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {HasDerivAt}\left(\operatorname {moment}\left(f, m\right), \operatorname {moment}\left(f, m + 1, x\right), x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.momentDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Domination at x/2 justifies differentiation under the integral for every moment.

**Theorem 1.13 (momentIterated).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(f\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb {R},\; \left(0 < t\right) \Rightarrow \left(0 \le \operatorname {f}\left(t\right)\right)\right) \Rightarrow \left(\left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)\right) \Rightarrow \left(\forall m \in \mathbb {N},\; \operatorname {Set.EqOn}\left(\operatorname {iteratedDeriv}\left(m, \operatorname {moment}\left(f, 0\right)\right), \operatorname {moment}\left(f, m\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.momentIterated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative identity iterates on the open positive half-line.

**Theorem 1.14 (laplaceCM).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(f\right)\right) \Rightarrow \left(\left(\forall t \in \mathbb {R},\; \left(0 < t\right) \Rightarrow \left(0 \le \operatorname {f}\left(t\right)\right)\right) \Rightarrow \left(\left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)\right) \Rightarrow \left(\operatorname {CompletelyMonotoneOn}\left(\operatorname {moment}\left(f, 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.laplaceCM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Smoothness follows from differentiation of every moment, and the two sign factors cancel inside the nonnegative integral.

**Definition 1.15 (coeff).**

$$\forall k \in \mathbb {N},\; \operatorname {coeff}\left(k\right) = \frac{\left(2\right)^{k} \cdot \operatorname {Real.Gamma}\left(k + \frac{1}{2}\right)}{\operatorname {Real.Gamma}\left(\frac{1}{2}\right)}$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The half-integer Gamma coefficient abbreviates the repeated factor in (3.7).

**Definition 1.16 (intPow).**

$$\forall m \in \mathbb {N},\; \operatorname {intPow}\left(m\right) = \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \left(1 + \left(v\right)^{2}\right)^{m}, 0, 1, \operatorname {volume}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.intPow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These compact polynomial integrals encode the coefficient sum.

**Definition 1.17 (intWeight).**

$$\forall m \in \mathbb {N},\; \operatorname {intWeight}\left(m\right) = \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \left(v\right)^{2} \cdot \left(1 - \left(v\right)^{2}\right) \cdot \left(1 + \left(v\right)^{2}\right)^{m}, 0, 1, \operatorname {volume}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.intWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is nonnegative on the unit interval and is the same weight that occurs in K.

**Theorem 1.18 (intPow rec).**

$$\forall m \in \mathbb {N},\; \left(2 \cdot m + 3\right) \cdot \operatorname {intPow}\left(m + 1\right) - 2 \cdot \left(m + 1\right) \cdot \operatorname {intPow}\left(m\right) = \left(2\right)^{m + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.intPow_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrate the derivative of v times (1+v-squared) to the power m+1.

**Theorem 1.19 (coeff zero).**

$$\operatorname {coeff}\left(0\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gamma factors cancel at index zero.

**Theorem 1.20 (coeff rec).**

$$\forall m \in \mathbb {N},\; \operatorname {coeff}\left(m + 1\right) = \left(2 \cdot m + 1\right) \cdot \operatorname {coeff}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gamma recurrence gives the odd-factor coefficient recurrence.

**Theorem 1.21 (coeff sum).**

$$\forall m \in \mathbb {N},\; \sum_{j \in \operatorname {Finset.range}\left(m + 1\right)} \left(\frac{\operatorname {coeff}\left(j\right)}{\operatorname {Nat.factorial}\left(j\right)}\right) = \frac{\operatorname {coeff}\left(m + 1\right)}{\left(2\right)^{m} \cdot \operatorname {Nat.factorial}\left(m\right)} \cdot \operatorname {intPow}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction combines the compact integral recurrence with the Gamma coefficient recurrence.

**Theorem 1.22 (intWeight eq).**

$$\forall m \in \mathbb {N},\; 2 \cdot \left(m + 1\right) \cdot \left(m + 2\right) \cdot \operatorname {intWeight}\left(m\right) = \left(2\right)^{m + 3} - \left(m + 4\right) \cdot \operatorname {intPow}\left(m + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.intWeight_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the polynomial weight and applying two consecutive integral recurrences evaluates the weighted combination.

**Theorem 1.23 (coeff factorial).**

$$\forall m \in \mathbb {N},\; \operatorname {coeff}\left(m + 1\right) \cdot \left(2\right)^{m} \cdot \operatorname {Nat.factorial}\left(m\right) = \operatorname {Nat.factorial}\left(2 \cdot m + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mathlib’s half-integer Gamma formula and the factorial–double-factorial identity convert the normalization into an odd factorial.

**Theorem 1.24 (u kernel coeff).**

$$\forall m \in \mathbb {N},\; \operatorname {u}\left(m + 3, -1, -3\right) = -\frac{\operatorname {coeff}\left(m + 3\right) \cdot \left(m + 1\right) \cdot \left(m + 2\right)}{\left(2\right)^{m + 1}} \cdot \operatorname {intWeight}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.u_kernel_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original coefficients at a=-1, b=-3 are negative weighted kernel coefficients.

**Theorem 1.25 (u kernel factorial).**

$$\forall m \in \mathbb {N},\; \operatorname {u}\left(m + 3, -1, -3\right) = \frac{-\operatorname {Nat.factorial}\left(2 \cdot m + 5\right)}{8 \cdot \left(4\right)^{m} \cdot \operatorname {Nat.factorial}\left(m\right)} \cdot \operatorname {intWeight}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.u_kernel_factorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalent factorial normalization is (2m+5)! divided by 8 times 4 to the m times m!. This is the normalization obtained by integrating the monomial Laplace term.

**Theorem 1.26 (u special).**

$$\forall m \in \mathbb {N},\; \operatorname {u}\left(m + 1, -1, -3\right) = -2 \cdot \operatorname {coeff}\left(m + 1\right) + \left(m + 2\right) \cdot \operatorname {Nat.factorial}\left(m\right) \cdot \sum_{j \in \operatorname {Finset.range}\left(m + 1\right)} \left(\frac{\operatorname {coeff}\left(j\right)}{\operatorname {Nat.factorial}\left(j\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.u_special` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substituting a=-1 and b=-3 isolates the common Gamma coefficient sum.

**Theorem 1.27 (u one zero).**

$$\operatorname {u}\left(1, -1, -3\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.u_one_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of x to the power -2 vanishes.

**Theorem 1.28 (u two zero).**

$$\operatorname {u}\left(2, -1, -3\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.u_two_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient of x to the power -4 also vanishes.

**Theorem 1.29 (D rec).**

$$\forall r \in \mathbb {N},\; \forall x \in \mathbb {R},\; \operatorname {D}\left(r + 3, x, -1\right) = \operatorname {D}\left(r + 2, x, -1\right) - \frac{\left(-1\right)^{r + 3} \cdot \operatorname {u}\left(r + 3, -1, -3\right)}{\left(x\right)^{2 \cdot \left(r + 3\right)}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.D_rec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding the top index to the finite sum gives the recurrence for successive remainders.

**Theorem 1.30 (D two).**

$$\forall x \in \mathbb {R},\; \operatorname {D}\left(2, x, -1\right) = \left(\left(x\right)^{2} - 1\right) \cdot \left(\operatorname {millsRatio}\left(x\right)\right)^{2} - 3 \cdot x \cdot \operatorname {millsRatio}\left(x\right) + 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.D_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two vanishing coefficients identify D at index two with the basic expression H.

**Definition 1.31 (J).**

$$\forall p \in \mathbb {R} \to \mathbb {R},\; \forall t \in \mathbb {R},\; \operatorname {J}\left(p, t\right) = \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \operatorname {p}\left(v\right) \cdot \operatorname {Real.exp}\left(\frac{-\left(\left(1 + \left(v\right)^{2}\right) \cdot \left(t\right)^{2}\right)}{4}\right), 0, 1, \operatorname {volume}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Gaussian average uses the fixed unit interval.

**Definition 1.32 (q0).**

$$\forall t \in \mathbb {R},\; \operatorname {q0}\left(t\right) = t \cdot \operatorname {J}\left(\operatorname {Function.const}\left(\mathbb {R}, 1\right), t\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.q0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed convolution kernel is q0.

**Definition 1.33 (q1).**

$$\forall t \in \mathbb {R},\; \operatorname {q1}\left(t\right) = \operatorname {J}\left(\operatorname {Function.const}\left(\mathbb {R}, 1\right), t\right) - \frac{\left(t\right)^{2}}{2} \cdot \operatorname {J}\left(v: \mathbb {R}\mapsto 1 + \left(v\right)^{2}, t\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.q1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first derivative of the convolution kernel has this explicit form.

**Definition 1.34 (q2).**

$$\forall t \in \mathbb {R},\; \operatorname {q2}\left(t\right) = \frac{\left(t\right)^{3}}{4} \cdot \operatorname {J}\left(v: \mathbb {R}\mapsto \left(1 + \left(v\right)^{2}\right)^{2}, t\right) - \frac{3 \cdot t}{2} \cdot \operatorname {J}\left(v: \mathbb {R}\mapsto 1 + \left(v\right)^{2}, t\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.q2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second derivative is a difference of two polynomial Gaussian averages.

**Definition 1.35 (K).**

$$\forall t \in \mathbb {R},\; \operatorname {K}\left(t\right) = \frac{\left(t\right)^{5}}{8} \cdot \operatorname {J}\left(v: \mathbb {R}\mapsto \left(v\right)^{2} \cdot \left(1 - \left(v\right)^{2}\right), t\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K is the positive Gaussian kernel for the basic Mills-ratio remainder.

**Theorem 1.36 (JDeriv).**

$$\forall p \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(p\right)\right) \Rightarrow \left(\forall t \in \mathbb {R},\; \operatorname {HasDerivAt}\left(\operatorname {J}\left(p\right), -\frac{t}{2} \cdot \operatorname {J}\left(v: \mathbb {R}\mapsto \operatorname {p}\left(v\right) \cdot \left(1 + \left(v\right)^{2}\right), t\right), t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.JDeriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation under the fixed interval integral, justified by a continuous derivative on compact parameter rectangles, inserts the factor -(t/2)(1+v-squared) into the Gaussian average.

**Theorem 1.37 (q0Deriv).**

$$\forall t \in \mathbb {R},\; \operatorname {HasDerivAt}\left(\operatorname {q0}, \operatorname {q1}\left(t\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.q0Deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product rule gives q1 as the derivative of q0.

**Theorem 1.38 (q1Deriv).**

$$\forall t \in \mathbb {R},\; \operatorname {HasDerivAt}\left(\operatorname {q1}, \operatorname {q2}\left(t\right), t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.q1Deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A second product-rule calculation gives q2.

**Theorem 1.39 (kernelIdentity).**

$$\forall t \in \mathbb {R},\; \operatorname {q2}\left(t\right) - \operatorname {q0}\left(t\right) + 3 \cdot t \cdot \operatorname {Real.exp}\left(-\frac{\left(t\right)^{2}}{2}\right) = \operatorname {K}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.kernelIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two applications of the fundamental theorem in the unit-interval variable remove the lower-degree Gaussian terms, leaving the nonnegative weight v-squared times (1-v-squared).

**Theorem 1.40 (JBound).**

$$\forall p \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(p\right)\right) \Rightarrow \left(\exists C \in \mathbb {R},\; \left(0 \le C\right) \land \left(\forall t \in \mathbb {R},\; \left\lVert \operatorname {J}\left(p, t\right) \right\rVert \le C\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.JBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gaussian factor is at most one, so compact boundedness of p gives a uniform bound on J.

**Theorem 1.41 (JMomentIntegrable).**

$$\forall p \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(p\right)\right) \Rightarrow \left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {J}\left(p, t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.JMomentIntegrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform bound on J reduces integrability to polynomial exponential moments.

**Theorem 1.42 (JMomentTendsto).**

$$\forall p \in \mathbb {R} \to \mathbb {R},\; \left(\operatorname {Continuous}\left(p\right)\right) \Rightarrow \left(\forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {Filter.Tendsto}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {J}\left(p, t\right), \operatorname {Filter.atTop}, \operatorname {nhds}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.JMomentTendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial exponential envelope tends to zero and controls all integration-by-parts boundary terms.

**Theorem 1.43 (laplaceIBP).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \forall g \in \mathbb {R} \to \mathbb {R},\; \forall x \in \mathbb {R},\; \left(\forall t \in \mathbb {R},\; \operatorname {HasDerivAt}\left(f, \operatorname {g}\left(t\right), t\right)\right) \Rightarrow \left(\left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right) \Rightarrow \left(\left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {g}\left(t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right) \Rightarrow \left(\left(\operatorname {Filter.Tendsto}\left(t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right), \operatorname {Filter.atTop}, \operatorname {nhds}\left(0\right)\right)\right) \Rightarrow \left(\operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {g}\left(t\right)\right) = x \cdot \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {f}\left(t\right)\right) - \operatorname {f}\left(0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.laplaceIBP` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fundamental theorem on the positive ray gives integration by parts when the weighted function and derivative are integrable and the infinite boundary vanishes.

**Theorem 1.44 (kernelLaplace).**

$$\forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\forall r \in \mathbb {R},\; \left(r = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {Real.exp}\left(-\frac{\left(t\right)^{2}}{2}\right)\right)\right) \Rightarrow \left(\left(\left(r\right)^{2} = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {q0}\left(t\right)\right)\right) \Rightarrow \left(\left(\left(x\right)^{2} - 1\right) \cdot \left(r\right)^{2} - 3 \cdot x \cdot r + 2 = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {K}\left(t\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.kernelLaplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating by parts twice transfers x-squared from the Laplace transform to q2. The Gaussian derivative accounts for the linear Mills term, and the kernel identity yields K.

**Definition 1.45 (expRemainder).**

$$\forall r \in \mathbb {N},\; \forall v \in \mathbb {R},\; \operatorname {expRemainder}\left(r, v\right) = \left(-1\right)^{r} \cdot \left(\operatorname {D5.S3.Analytic.ExpRemainderDifferences.R}\left(r, -v\right) + \frac{\left(-v\right)^{r}}{\operatorname {Nat.factorial}\left(r\right)}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponential remainder R through degree r is evaluated at -v and its top Taylor monomial is restored, then multiplied by the alternating sign. This gives the signed remainder after r terms.

**Theorem 1.46 (expRemainder eq).**

$$\forall r \in \mathbb {N},\; \forall v \in \mathbb {R},\; \operatorname {expRemainder}\left(r, v\right) = \left(-1\right)^{r} \cdot \left(\operatorname {Real.exp}\left(-v\right) - \sum_{j \in \operatorname {Finset.range}\left(r\right)} \left(\frac{\left(-v\right)^{j}}{\operatorname {Nat.factorial}\left(j\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainder_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Removing the last term from the degree-r Taylor sum gives the finite-remainder expression for every r, including zero, when the sum is empty and the remainder equals exp(-v).

**Theorem 1.47 (expRemainderBounds).**

$$\forall r \in \mathbb {N},\; \forall v \in \mathbb {R},\; \left(0 \le v\right) \Rightarrow \left(\left(0 \le \operatorname {expRemainder}\left(r, v\right)\right) \land \left(\operatorname {expRemainder}\left(r, v\right) \le \frac{\left(v\right)^{r}}{\operatorname {Nat.factorial}\left(r\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderBounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taylor’s theorem with a Lagrange remainder gives positivity and the polynomial upper bound. The order-zero case uses exp(-v) between zero and one.

**Theorem 1.48 (expRemainderContinuous).**

$$\forall r \in \mathbb {N},\; \operatorname {Continuous}\left(\operatorname {expRemainder}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderContinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite sum and exponential are continuous.

**Theorem 1.49 (expRemainderRec).**

$$\forall r \in \mathbb {N},\; \forall v \in \mathbb {R},\; \operatorname {expRemainder}\left(r + 1, v\right) = \frac{\left(v\right)^{r}}{\operatorname {Nat.factorial}\left(r\right)} - \operatorname {expRemainder}\left(r, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderRec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next signed remainder is the current Taylor monomial minus the preceding signed remainder.

**Definition 1.50 (remainderKernel).**

$$\forall r \in \mathbb {N},\; \forall t \in \mathbb {R},\; \operatorname {remainderKernel}\left(r, t\right) = \frac{\left(t\right)^{5}}{8} \cdot \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \left(v\right)^{2} \cdot \left(1 - \left(v\right)^{2}\right) \cdot \operatorname {expRemainder}\left(r, \frac{\left(1 + \left(v\right)^{2}\right) \cdot \left(t\right)^{2}}{4}\right), 0, 1, \operatorname {volume}\right)$$

*Formalization.* `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel for every truncation index replaces the Gaussian factor of K by its signed finite Taylor remainder.

**Theorem 1.51 (remainderKernelContinuous).**

$$\forall r \in \mathbb {N},\; \operatorname {Continuous}\left(\operatorname {remainderKernel}\left(r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelContinuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuous dependence of an integral over the compact unit interval gives continuity of each remainder kernel.

**Theorem 1.52 (remainderKernelBounds).**

$$\forall r \in \mathbb {N},\; \forall t \in \mathbb {R},\; \left(0 \le t\right) \Rightarrow \left(\left(0 \le \operatorname {remainderKernel}\left(r, t\right)\right) \land \left(\operatorname {remainderKernel}\left(r, t\right) \le \left(t\right)^{2 \cdot r + 5}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelBounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit-interval weight lies between zero and one, and the Taylor remainder bound gives a polynomial envelope for the kernel.

**Theorem 1.53 (remainderKernelMoments).**

$$\forall r \in \mathbb {N},\; \forall m \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{m} \cdot \operatorname {Real.exp}\left(-\left(x \cdot t\right)\right) \cdot \operatorname {remainderKernel}\left(r, t\right), \operatorname {Set.Ioi}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelMoments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial kernel envelope gives integrability after multiplication by every additional moment and positive-rate exponential.

**Theorem 1.54 (remainderKernelRec).**

$$\forall r \in \mathbb {N},\; \forall t \in \mathbb {R},\; \operatorname {remainderKernel}\left(r + 1, t\right) = \frac{\left(t\right)^{2 \cdot r + 5}}{8 \cdot \left(4\right)^{r} \cdot \operatorname {Nat.factorial}\left(r\right)} \cdot \operatorname {intervalIntegral}\left(v: \mathbb {R}\mapsto \left(v\right)^{2} \cdot \left(1 - \left(v\right)^{2}\right) \cdot \left(1 + \left(v\right)^{2}\right)^{r}, 0, 1, \operatorname {volume}\right) - \operatorname {remainderKernel}\left(r, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelRec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential-remainder recurrence gives the kernel recurrence with the same compact polynomial moment as the source coefficient.

**Theorem 1.55 (remainderLaplaceRec).**

$$\forall r \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\operatorname {moment}\left(\operatorname {remainderKernel}\left(r + 1\right), 0, x\right) = \frac{\frac{\operatorname {Nat.factorial}\left(2 \cdot r + 5\right)}{8 \cdot \left(4\right)^{r} \cdot \operatorname {Nat.factorial}\left(r\right)} \cdot \operatorname {intWeight}\left(r\right)}{\left(x\right)^{2 \cdot r + 6}} - \operatorname {moment}\left(\operatorname {remainderKernel}\left(r\right), 0, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderLaplaceRec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating the kernel recurrence evaluates its monomial by the Gamma integral and gives the recurrence for successive Laplace remainders.

**Theorem 1.56 (remainderRepresentation).**

$$\forall r \in \mathbb {N},\; \forall x \in \mathbb {R},\; \left(0 < x\right) \Rightarrow \left(\left(-1\right)^{r} \cdot \operatorname {D}\left(r + 2, x, -1\right) = \operatorname {moment}\left(\operatorname {remainderKernel}\left(r\right), 0, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderRepresentation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The basic kernel identity gives the order-zero case. Induction combines the coefficient identity with the finite remainder recurrence to obtain the exact positive Laplace representation at every truncation index.

**Theorem 1.57 (Complete monotonicity of every signed remainder).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XuYangMillsRemainder/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/xu-yang-2026-mills-remainder-cm` (proved) by `D5/S3/Analytic/XuYangMillsRemainder/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"xu-yang-2026-mills-remainder-cm","declaration_gid":"D5/S3/Analytic/XuYangMillsRemainder/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hui-Zuo Xu and Zhen-Hang Yang (2026). *Higher order monotonicity involving the Mills ratio with applications*. DOI: [10.1186/s13660-026-03505-9](https://doi.org/10.1186/s13660-026-03505-9). URL: <https://doi.org/10.1186/s13660-026-03505-9>.

*Commentary.*

For every natural n≥2 the signed remainder has a nonnegative Laplace kernel. Its polynomial envelope makes every exponentially weighted moment integrable. Differentiation under the integral gives C-infinity smoothness and the sign of every derivative on the positive half-line.

## References

- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.CompletelyMonotoneOn`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.D`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.D_rec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.D_two`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.J`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.JBound`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.JDeriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.JMomentIntegrable`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.JMomentTendsto`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.K`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.Y`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.claim`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_factorial`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_rec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_sum`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.coeff_zero`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.convolutionClosed`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainder`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderBounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderContinuous`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainderRec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.expRemainder_eq`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.intPow`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.intPow_rec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.intWeight`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.intWeight_eq`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.kernelIdentity`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.kernelLaplace`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.laplaceCM`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.laplaceIBP`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.millsLaplace`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.millsLaplaceIntegrable`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.millsRatio`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.millsSquareConvolution`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.moment`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.momentDeriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.momentIterated`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.q0`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.q0Deriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.q1`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.q1Deriv`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.q2`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernel`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelBounds`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelContinuous`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelMoments`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderKernelRec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderLaplaceRec`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.remainderRepresentation`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.result`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u_kernel_coeff`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u_kernel_factorial`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u_one_zero`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u_special`
- Truth anchor: `D5/S3/Analytic/XuYangMillsRemainder/Result.u_two_zero`
- Dependency: [D5/S3/Analytic/ExpRemainderDifferences](../ExpRemainderDifferences.md)
- Dependency: [D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments](../ExponentialSum/TwoScaleEndpointMoments.md)
- Dependency: [D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay](../../FluidDynamics/Fourier/PeriodicAllenCahnDecay.md)
