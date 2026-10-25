# A gamma-gamma counterexample to NBU

## Abstract

The gamma-gamma family does not universally satisfy the NBU property.

**Definition 1.1 (besselK).**

$$\forall nu \in \operatorname {Real}\left(\right),\; \forall z \in \operatorname {Real}\left(\right),\; \operatorname {besselK}\left(nu, z\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {MeasureTheory.Measure.restrict}\left(\operatorname {MeasureTheory.volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), \lambda t: \operatorname {Real}\left(\right), (\operatorname {Real.exp}\left(-((z) \cdot (\operatorname {Real.cosh}\left(t\right)))\right)) \cdot (\operatorname {Real.cosh}\left((nu) \cdot (t)\right))\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.besselK` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Modified Bessel functions, integral representations*. DOI: [10.18434/T4J30S](https://doi.org/10.18434/T4J30S). URL: <https://dlmf.nist.gov/10.32.E9>.

*Commentary.*

DLMF 10.32.9: “K_ν(z) = ∫_0^∞ exp(−z cosh t) cosh(νt) dt, |ph z| < ½π”. For real nu and z>0 this is the standard modified Bessel function of the second kind. Only positive z is used below. The real integral gives a total definition outside that domain.

**Definition 1.2 (density).**

$$\forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; \forall alpha \in \operatorname {Real}\left(\right),\; \forall u \in \operatorname {Real}\left(\right),\; \operatorname {density}\left(a, b, alpha, u\right) = (\frac{((2) \cdot (((a) \cdot (b))^{\frac{(a) + (b)}{2}})) \cdot ((u)^{(\frac{(a) + (b)}{2}) - (1)})}{((\operatorname {Real.Gamma}\left(a\right)) \cdot (\operatorname {Real.Gamma}\left(b\right))) \cdot ((alpha)^{\frac{(a) + (b)}{2}})}) \cdot (\operatorname {besselK}\left((a) - (b), (2) \cdot (\operatorname {Real.sqrt}\left(\frac{((a) \cdot (b)) \cdot (u)}{alpha}\right))\right))$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.density` (`✓ std3`).

*Citation.* Á. Baricz, S. Ponnusamy and M. Vuorinen (2011). *Functional inequalities for modified Bessel functions*. DOI: [10.1016/j.exmath.2011.07.001](https://doi.org/10.1016/j.exmath.2011.07.001). URL: <https://arxiv.org/abs/1009.4814v2>.

*Commentary.*

Section 4, printed page 10: “The probability density function fₐ,ᵦ,α : (0, ∞) → (0, ∞) of the three parameter gamma-gamma random variable is defined by (see [21])” followed by fₐ,ᵦ,α(u)=2(ab)^((a+b)/2)u^((a+b)/2−1)/(Γ(a)Γ(b)α^((a+b)/2)) Kₐ₋ᵦ(2√((ab/α)u)), and “where a, b > 0 are the distribution shaping parameters, Kν stands for the modified Bessel function of the second kind, and α > 0 is the mean of the gamma-gamma random variable.” Real powers, Real.Gamma and the nonnegative square root implement that formula exactly.

**Definition 1.3 (survival).**

$$\forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; \forall alpha \in \operatorname {Real}\left(\right),\; \forall u \in \operatorname {Real}\left(\right),\; \operatorname {survival}\left(a, b, alpha, u\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {MeasureTheory.Measure.restrict}\left(\operatorname {MeasureTheory.volume}\left(\right), \operatorname {Set.Ioi}\left(u\right)\right), \lambda t: \operatorname {Real}\left(\right), \operatorname {density}\left(a, b, alpha, t\right)\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.survival` (`✓ std3`).

*Citation.* Á. Baricz, S. Ponnusamy and M. Vuorinen (2011). *Functional inequalities for modified Bessel functions*. DOI: [10.1016/j.exmath.2011.07.001](https://doi.org/10.1016/j.exmath.2011.07.001). URL: <https://arxiv.org/abs/1009.4814v2>.

*Commentary.*

The survival function is the Lebesgue integral of the source density over t>u. Endpoints have zero Lebesgue measure.

**Definition 1.4 (claim).**

$$claim = \left(\forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; \forall alpha \in \operatorname {Real}\left(\right),\; (0 < a) \Rightarrow ((0 < b) \Rightarrow ((0 < alpha) \Rightarrow (\forall u1 \in \operatorname {Real}\left(\right),\; \forall u2 \in \operatorname {Real}\left(\right),\; (0 < u1) \Rightarrow ((0 < u2) \Rightarrow (\operatorname {survival}\left(a, b, alpha, (u1) + (u2)\right) \le (\operatorname {survival}\left(a, b, alpha, u1\right)) \cdot (\operatorname {survival}\left(a, b, alpha, u2\right)))))))\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.claim` (`✓ std3`).

*Citation.* Á. Baricz, S. Ponnusamy and M. Vuorinen (2011). *Functional inequalities for modified Bessel functions*. DOI: [10.1016/j.exmath.2011.07.001](https://doi.org/10.1016/j.exmath.2011.07.001). URL: <https://arxiv.org/abs/1009.4814v2>.

*Commentary.*

Section 5, printed page 13: “By definition a life distribution satisfies the new-is-better-than-used (NBU) property if u ↦ log F̄(u) is sub-additive, i.e. F̄(u₁ + u₂) ≤ F̄(u₁)F̄(u₂) for all u₁, u₂ > 0.” The question on the same page is: “Question 8. Is it true that the gamma-gamma distribution satisfies the NBU property?” The assertion quantifies over all positive shape parameters, means and positive u₁,u₂. It has exactly the inequality and positive-domain quantifiers asked there.

**Definition 1.5 (kernel).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall s \in \operatorname {Real}\left(\right),\; \operatorname {kernel}\left(u, s\right) = \operatorname {Real.exp}\left((-(s)) - (\frac{u}{s})\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.kernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This exponential kernel is the integrand in the survival representation.

**Theorem 1.6 (kernel integrable).**

$$\forall u \in \operatorname {Real}\left(\right),\; (0 \le u) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(\operatorname {kernel}\left(u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative u and positive s the kernel lies between zero and exp(−s). Measurability and comparison with the integrable exponential prove integrability.

**Theorem 1.7 (density one).**

$$\forall t \in \operatorname {Real}\left(\right),\; \operatorname {density}\left(1, 1, 1, t\right) = (2) \cdot (\operatorname {besselK}\left(0, (2) \cdot (\operatorname {Real.sqrt}\left(t\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.density_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gamma(1)=1 and the real-power identities reduce the source density to 2K₀(2√t).

**Theorem 1.8 (bessel mix).**

$$\forall t \in \operatorname {Real}\left(\right),\; (0 < t) \Rightarrow ((2) \cdot (\operatorname {besselK}\left(0, (2) \cdot (\operatorname {Real.sqrt}\left(t\right))\right)) = \operatorname {MeasureTheory.integral}\left(\operatorname {MeasureTheory.Measure.restrict}\left(\operatorname {MeasureTheory.volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), \lambda s: \operatorname {Real}\left(\right), (\frac{1}{s}) \cdot (\operatorname {kernel}\left(t, s\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.bessel_mix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The change s=√t exp(x), using integral_comp_exp and translation invariance, turns the exponential kernel into exp(−2√t cosh(x)). Evenness and integral_comp_abs halve the whole-line integral. These identities prove the stated mixture formula without assuming a Bessel identity.

**Theorem 1.9 (mix integrable inner).**

$$\forall s \in \operatorname {Real}\left(\right),\; \forall u \in \operatorname {Real}\left(\right),\; (0 < s) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(\lambda t: \operatorname {Real}\left(\right), (\frac{1}{s}) \cdot (\operatorname {kernel}\left(t, s\right)), \operatorname {Set.Ioi}\left(u\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.mix_integrable_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At fixed positive s the integrand is a constant times exp(−t/s), hence is integrable on every upper half-line.

**Theorem 1.10 (mix integral inner).**

$$\forall s \in \operatorname {Real}\left(\right),\; \forall u \in \operatorname {Real}\left(\right),\; (0 < s) \Rightarrow (\operatorname {MeasureTheory.integral}\left(\operatorname {MeasureTheory.Measure.restrict}\left(\operatorname {MeasureTheory.volume}\left(\right), \operatorname {Set.Ioi}\left(u\right)\right), \lambda t: \operatorname {Real}\left(\right), (\frac{1}{s}) \cdot (\operatorname {kernel}\left(t, s\right))\right) = \operatorname {kernel}\left(u, s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.mix_integral_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper-half-line exponential integral evaluates to exp(−s−u/s).

**Theorem 1.11 (survival mix).**

$$\forall u \in \operatorname {Real}\left(\right),\; (0 < u) \Rightarrow (\operatorname {survival}\left(1, 1, 1, u\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {MeasureTheory.Measure.restrict}\left(\operatorname {MeasureTheory.volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), \lambda s: \operatorname {Real}\left(\right), \operatorname {kernel}\left(u, s\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.survival_mix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inner integral of the nonnegative mixture is the integrable kernel. integrable_prod_iff establishes product integrability and integral_integral_swap exchanges the two integrations. This connects the original Bessel density to the scalar integral used for the bounds.

**Theorem 1.12 (kernel inc).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; (0 < a) \Rightarrow ((a \le b) \Rightarrow (((a) \cdot (b) \le u) \Rightarrow (\operatorname {kernel}\left(u, a\right) \le \operatorname {kernel}\left(u, b\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.kernel_inc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparison of the exponents reduces to the sign of (b−a)(u−ab). This gives the monotone comparison on the corresponding side of the peak.

**Theorem 1.13 (kernel dec).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; (0 < a) \Rightarrow ((a \le b) \Rightarrow ((u \le (a) \cdot (b)) \Rightarrow (\operatorname {kernel}\left(u, b\right) \le \operatorname {kernel}\left(u, a\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.kernel_dec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Comparison of the exponents reduces to the sign of (b−a)(u−ab). This gives the monotone comparison on the corresponding side of the peak.

**Theorem 1.14 (kernel lower).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall a \in \operatorname {Real}\left(\right),\; \forall b \in \operatorname {Real}\left(\right),\; \forall s \in \operatorname {Real}\left(\right),\; (0 < a) \Rightarrow ((s \in \operatorname {Set.Icc}\left(a, b\right)) \Rightarrow (\operatorname {min}\left(\operatorname {kernel}\left(u, a\right), \operatorname {kernel}\left(u, b\right)\right) \le \operatorname {kernel}\left(u, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.kernel_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every value on a positive interval is at least the smaller endpoint value. Splitting at s²=u uses the increasing or decreasing comparison, including intervals that cross the peak.

**Definition 1.15 (poly).**

$$\forall x \in \operatorname {Real}\left(\right),\; \operatorname {poly}\left(x\right) = \operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(6\right), \lambda k: \operatorname {Nat}\left(\right), \frac{(x)^{k}}{\operatorname {Nat.factorial}\left(k\right)}\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.poly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The degree-five exponential Taylor polynomial has six terms.

**Definition 1.16 (err).**

$$\forall x \in \operatorname {Real}\left(\right),\; \operatorname {err}\left(x\right) = ((\operatorname {abs}\left(x\right))^{6}) \cdot (\frac{7}{4320})$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.err` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the rational remainder bound from Real.exp_bound at order six.

**Theorem 1.17 (exp scaled bounds).**

$$\forall y \in \operatorname {Real}\left(\right),\; (0 \le y) \Rightarrow ((y \le 32) \Rightarrow ((0 \le (\operatorname {poly}\left(\frac{-(y)}{32}\right)) - (\operatorname {err}\left(\frac{-(y)}{32}\right))) \Rightarrow ((((\operatorname {poly}\left(\frac{-(y)}{32}\right)) - (\operatorname {err}\left(\frac{-(y)}{32}\right)))^{32} \le \operatorname {Real.exp}\left(-(y)\right)) \land (\operatorname {Real.exp}\left(-(y)\right) \le ((\operatorname {poly}\left(\frac{-(y)}{32}\right)) + (\operatorname {err}\left(\frac{-(y)}{32}\right)))^{32}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.exp_scaled_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real.exp_bound encloses exp(−y/32). Both endpoints are nonnegative; raising to the 32nd power preserves their order and exp_nat_mul recovers exp(−y).

**Theorem 1.18 (exp lower cert).**

$$\forall y \in \operatorname {Real}\left(\right),\; \forall l \in \operatorname {Real}\left(\right),\; (0 \le y) \Rightarrow ((y \le 32) \Rightarrow ((0 \le (\operatorname {poly}\left(\frac{-(y)}{32}\right)) - (\operatorname {err}\left(\frac{-(y)}{32}\right))) \Rightarrow ((l \le ((\operatorname {poly}\left(\frac{-(y)}{32}\right)) - (\operatorname {err}\left(\frac{-(y)}{32}\right)))^{32}) \Rightarrow (l \le \operatorname {Real.exp}\left(-(y)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.exp_lower_cert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational lower endpoint below the lower Taylor power also bounds the exponential from below.

**Theorem 1.19 (exp upper cert).**

$$\forall y \in \operatorname {Real}\left(\right),\; \forall r \in \operatorname {Real}\left(\right),\; (0 \le y) \Rightarrow ((y \le 32) \Rightarrow ((0 \le (\operatorname {poly}\left(\frac{-(y)}{32}\right)) - (\operatorname {err}\left(\frac{-(y)}{32}\right))) \Rightarrow ((((\operatorname {poly}\left(\frac{-(y)}{32}\right)) + (\operatorname {err}\left(\frac{-(y)}{32}\right)))^{32} \le r) \Rightarrow (\operatorname {Real.exp}\left(-(y)\right) \le r))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.exp_upper_cert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational upper endpoint above the upper Taylor power also bounds the exponential from above.

**Theorem 1.20 (grid integral lower).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall h \in \operatorname {Real}\left(\right),\; (0 \le u) \Rightarrow ((0 < h) \Rightarrow (\forall n \in \operatorname {Nat}\left(\right),\; \forall c \in \operatorname {Nat}\left(\right) \to \operatorname {Real}\left(\right),\; (\forall k \in \operatorname {Nat}\left(\right),\; (k < n) \Rightarrow (\forall s \in \operatorname {Real}\left(\right),\; (s \in \operatorname {Set.Ico}\left((k) \cdot (h), ((k) + (1)) \cdot (h)\right)) \Rightarrow (c\left(k\right) \le \operatorname {kernel}\left(u, s\right)))) \Rightarrow ((h) \cdot (\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(n\right), \lambda k: \operatorname {Nat}\left(\right), c\left(k\right)\right)) \le \operatorname {intervalIntegral}\left(\lambda s: \operatorname {Real}\left(\right), \operatorname {kernel}\left(u, s\right), 0, (n) \cdot (h), \operatorname {MeasureTheory.volume}\left(\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.grid_integral_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After s=h x, sum_Ico_le_integral_of_le compares the lower rectangles with the integral. IntervalIntegrable.comp_mul_left transfers kernel_integrable to the rescaled interval; integral_comp_mul_left returns the original scale. The lower bounds include the left endpoints of the cells.

**Theorem 1.21 (grid integral upper).**

$$\forall u \in \operatorname {Real}\left(\right),\; \forall h \in \operatorname {Real}\left(\right),\; (0 \le u) \Rightarrow ((0 < h) \Rightarrow (\forall n \in \operatorname {Nat}\left(\right),\; \forall c \in \operatorname {Nat}\left(\right) \to \operatorname {Real}\left(\right),\; (\forall k \in \operatorname {Nat}\left(\right),\; (k < n) \Rightarrow (\forall s \in \operatorname {Real}\left(\right),\; (s \in \operatorname {Set.Ico}\left((k) \cdot (h), ((k) + (1)) \cdot (h)\right)) \Rightarrow ((0 < s) \Rightarrow (\operatorname {kernel}\left(u, s\right) \le c\left(k\right))))) \Rightarrow (\operatorname {intervalIntegral}\left(\lambda s: \operatorname {Real}\left(\right), \operatorname {kernel}\left(u, s\right), 0, (n) \cdot (h), \operatorname {MeasureTheory.volume}\left(\right)\right) \le (h) \cdot (\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(n\right), \lambda k: \operatorname {Nat}\left(\right), c\left(k\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.grid_integral_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After s=h x, integral_le_sum_Ico_of_le compares the integral with the upper rectangles. At x=0 the rescaled integrand is assigned c(0), since kernel(u,0)=1 need not satisfy the first rectangle bound. It equals the original integrand on the open interval, so integral_congr_uIoo preserves its integral and IntervalIntegrable.congr_uIoo preserves integrability. Positive left endpoints satisfy the cell bounds; integral_comp_mul_left returns the original scale.

**Definition 1.22 (lowerData).**

$$\operatorname {lowerData}\left(\right): \operatorname {Nat}\left(\right) \to \operatorname {Real}\left(\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.lowerData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 200 rational rectangle heights are stored in a balanced decision tree, in millionths. Values beyond the final index equal the last leaf; only the stated finite grid is used. The endpoint certificates below check each relevant entry exactly.

**Definition 1.23 (upperData).**

$$\operatorname {upperData}\left(\right): \operatorname {Nat}\left(\right) \to \operatorname {Real}\left(\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.upperData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The 96 rational rectangle heights are stored in a balanced decision tree, in millionths. Values beyond the final index equal the last leaf; only the stated finite grid is used. The endpoint certificates below check each relevant entry exactly.

**Definition 1.24 (lowerY).**

$$\forall k \in \operatorname {Nat}\left(\right),\; \operatorname {lowerY}\left(k\right) = \operatorname {max}\left((\frac{k}{25}) + (\frac{1}{\frac{k}{25}}), (\frac{(k) + (1)}{25}) + (\frac{1}{\frac{(k) + (1)}{25}})\right)$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.lowerY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the larger endpoint exponent on the lower grid. Natural indices in the formula are coerced to real numbers.

**Definition 1.25 (upperY).**

$$\forall k \in \operatorname {Nat}\left(\right),\; \operatorname {upperY}\left(k\right) = \operatorname {ite} (k \le 7) ((\frac{(k) + (1)}{12}) + (\frac{\frac{1}{2}}{\frac{(k) + (1)}{12}})) ((\frac{k}{12}) + (\frac{\frac{1}{2}}{\frac{k}{12}}))$$

*Formalization.* `D5/S3/Analytic/GammaGammaNBU/Result.upperY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Indices at most seven use the right endpoint; indices above seven use the left endpoint. The separate peak bound replaces index eight. Natural indices in real expressions are coerced to real numbers.

**Theorem 1.26 (lowerCert0).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((0 \le k) \land (k < 8)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.27 (lowerCert8).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((8 \le k) \land (k < 16)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.28 (lowerCert16).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((16 \le k) \land (k < 24)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.29 (lowerCert24).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((24 \le k) \land (k < 32)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert24` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.30 (lowerCert32).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((32 \le k) \land (k < 40)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.31 (lowerCert40).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((40 \le k) \land (k < 48)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert40` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.32 (lowerCert48).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((48 \le k) \land (k < 56)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert48` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.33 (lowerCert56).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((56 \le k) \land (k < 64)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert56` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.34 (lowerCert64).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((64 \le k) \land (k < 72)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.35 (lowerCert72).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((72 \le k) \land (k < 80)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert72` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.36 (lowerCert80).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((80 \le k) \land (k < 88)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert80` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.37 (lowerCert88).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((88 \le k) \land (k < 96)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert88` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.38 (lowerCert96).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((96 \le k) \land (k < 104)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert96` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.39 (lowerCert104).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((104 \le k) \land (k < 112)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert104` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.40 (lowerCert112).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((112 \le k) \land (k < 120)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert112` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.41 (lowerCert120).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((120 \le k) \land (k < 128)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert120` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.42 (lowerCert128).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((128 \le k) \land (k < 136)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert128` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.43 (lowerCert136).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((136 \le k) \land (k < 144)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert136` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.44 (lowerCert144).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((144 \le k) \land (k < 152)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert144` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.45 (lowerCert152).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((152 \le k) \land (k < 160)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert152` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.46 (lowerCert160).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((160 \le k) \land (k < 168)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert160` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.47 (lowerCert168).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((168 \le k) \land (k < 176)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert168` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.48 (lowerCert176).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((176 \le k) \land (k < 184)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert176` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.49 (lowerCert184).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((184 \le k) \land (k < 192)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert184` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.50 (lowerCert192).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((192 \le k) \land (k < 200)) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert192` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.51 (lower certificate).**

$$\forall k \in \operatorname {Nat}\left(\right),\; (k < 200) \Rightarrow ((k \ne 0) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {Real.exp}\left(-(\operatorname {lowerY}\left(k\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lower_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disjoint blocks cover the stated finite range; the exceptional cell is handled directly in the integral estimate.

**Theorem 1.52 (upperCert0).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((0 \le k) \land (k < 8)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.53 (upperCert8).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((8 \le k) \land (k < 16)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.54 (upperCert16).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((16 \le k) \land (k < 24)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.55 (upperCert24).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((24 \le k) \land (k < 32)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert24` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.56 (upperCert32).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((32 \le k) \land (k < 40)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.57 (upperCert40).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((40 \le k) \land (k < 48)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert40` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.58 (upperCert48).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((48 \le k) \land (k < 56)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert48` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.59 (upperCert56).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((56 \le k) \land (k < 64)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert56` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.60 (upperCert64).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((64 \le k) \land (k < 72)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.61 (upperCert72).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((72 \le k) \land (k < 80)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert72` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.62 (upperCert80).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((80 \le k) \land (k < 88)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert80` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.63 (upperCert88).**

$$\forall k \in \operatorname {Nat}\left(\right),\; ((88 \le k) \land (k < 96)) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upperCert88` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For these eight indices the rational Taylor inequalities certify the endpoint exponential bounds. Every arithmetic comparison is exact.

**Theorem 1.64 (upper certificate).**

$$\forall k \in \operatorname {Nat}\left(\right),\; (k < 96) \Rightarrow ((k \ne 8) \Rightarrow (\operatorname {Real.exp}\left(-(\operatorname {upperY}\left(k\right))\right) \le \operatorname {upperData}\left(k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upper_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The disjoint blocks cover the stated finite range; the exceptional cell is handled directly in the integral estimate.

**Theorem 1.65 (peak upper).**

$$\forall s \in \operatorname {Real}\left(\right),\; (0 < s) \Rightarrow (\operatorname {kernel}\left(\frac{1}{2}, s\right) \le \frac{1}{4})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.peak_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square inequality (s−7/10)²≥0 gives s+(1/2)/s≥7/5. The rational Taylor upper bound proves exp(−7/5)≤1/4.

**Theorem 1.66 (lower cell).**

$$\forall k \in \operatorname {Nat}\left(\right),\; (k < 200) \Rightarrow (\forall s \in \operatorname {Real}\left(\right),\; (s \in \operatorname {Set.Ico}\left(\frac{k}{25}, \frac{(k) + (1)}{25}\right)) \Rightarrow (\operatorname {lowerData}\left(k\right) \le \operatorname {kernel}\left(1, s\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lower_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Endpoint exponential bounds and monotonicity give this lower bound throughout each left-closed, right-open cell. The first lower cell has height zero, which also bounds the value at s=0.

**Theorem 1.67 (upper cell).**

$$\forall k \in \operatorname {Nat}\left(\right),\; (k < 96) \Rightarrow (\forall s \in \operatorname {Real}\left(\right),\; (0 < s) \Rightarrow ((s \in \operatorname {Set.Ico}\left(\frac{k}{12}, \frac{(k) + (1)}{12}\right)) \Rightarrow (\operatorname {kernel}\left(\frac{1}{2}, s\right) \le \operatorname {upperData}\left(k\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.upper_cell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Endpoint exponential bounds and monotonicity give this upper bound at every positive point of each left-closed, right-open cell. The cell containing √(1/2) uses the peak bound 1/4. The value at s=0 is excluded and is handled by the integral endpoint replacement.

**Theorem 1.68 (lowerSum0).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((0) + (i)\right)\right) = \frac{40821}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.69 (lowerSum8).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((8) + (i)\right)\right) = \frac{140009}{250000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.70 (lowerSum16).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((16) + (i)\right)\right) = \frac{1001311}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.71 (lowerSum24).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((24) + (i)\right)\right) = \frac{529071}{500000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum24` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.72 (lowerSum32).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((32) + (i)\right)\right) = \frac{187031}{200000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum32` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.73 (lowerSum40).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((40) + (i)\right)\right) = \frac{769587}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum40` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.74 (lowerSum48).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((48) + (i)\right)\right) = \frac{609471}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum48` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.75 (lowerSum56).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((56) + (i)\right)\right) = \frac{471657}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum56` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.76 (lowerSum64).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((64) + (i)\right)\right) = \frac{359589}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum64` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.77 (lowerSum72).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((72) + (i)\right)\right) = \frac{67839}{250000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum72` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.78 (lowerSum80).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((80) + (i)\right)\right) = \frac{203283}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum80` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.79 (lowerSum88).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((88) + (i)\right)\right) = \frac{151463}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum88` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.80 (lowerSum96).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((96) + (i)\right)\right) = \frac{28097}{250000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum96` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.81 (lowerSum104).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((104) + (i)\right)\right) = \frac{8313}{100000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum104` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.82 (lowerSum112).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((112) + (i)\right)\right) = \frac{6133}{100000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum112` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.83 (lowerSum120).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((120) + (i)\right)\right) = \frac{9031}{200000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum120` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.84 (lowerSum128).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((128) + (i)\right)\right) = \frac{3319}{100000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum128` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.85 (lowerSum136).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((136) + (i)\right)\right) = \frac{24361}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum136` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.86 (lowerSum144).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((144) + (i)\right)\right) = \frac{17861}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum144` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.87 (lowerSum152).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((152) + (i)\right)\right) = \frac{13081}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum152` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.88 (lowerSum160).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((160) + (i)\right)\right) = \frac{2393}{250000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum160` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.89 (lowerSum168).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((168) + (i)\right)\right) = \frac{6999}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum168` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.90 (lowerSum176).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((176) + (i)\right)\right) = \frac{639}{125000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum176` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.91 (lowerSum184).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((184) + (i)\right)\right) = \frac{3733}{1000000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum184` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.92 (lowerSum192).**

$$\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(8\right), \lambda i: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left((192) + (i)\right)\right) = \frac{109}{40000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum192` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This eight-cell sum is an exact rational identity.

**Theorem 1.93 (lower sum).**

$$\frac{2731}{10000} \le (\frac{1}{25}) \cdot (\operatorname {Finset.sum}\left(\operatorname {Finset.range}\left(200\right), \lambda k: \operatorname {Nat}\left(\right), \operatorname {lowerData}\left(k\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.lower_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the eight-cell rational identities gives a lower sum of 1712627/6250000=0.27402032, which exceeds 0.2731.

**Theorem 1.94 (witness lower).**

$$\frac{2731}{10000} \le \operatorname {survival}\left(1, 1, 1, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.witness_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 200 lower rectangles on [0,8] bound the integral from below; the remaining integrand is nonnegative.

**Theorem 1.95 (witness upper).**

$$\operatorname {survival}\left(1, 1, 1, \frac{1}{2}\right) \le \frac{467}{1000}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.witness_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The 96 upper rectangles on [0,8] sum to 1115597/2400000<0.466. Beyond eight the kernel is bounded by exp(−s), whose integral is exp(−8)≤0.001. Thus the survival value is at most 0.467.

**Theorem 1.96 (result).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaGammaNBU/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/baricz-ponnusamy-vuorinen-2011-gamma-gamma-nbu` (refuted) by `D5/S3/Analytic/GammaGammaNBU/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"baricz-ponnusamy-vuorinen-2011-gamma-gamma-nbu","declaration_gid":"D5/S3/Analytic/GammaGammaNBU/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Á. Baricz, S. Ponnusamy and M. Vuorinen (2011). *Functional inequalities for modified Bessel functions*. DOI: [10.1016/j.exmath.2011.07.001](https://doi.org/10.1016/j.exmath.2011.07.001). URL: <https://arxiv.org/abs/1009.4814v2>.

*Commentary.*

Take a=b=alpha=1 and u1=u2=1/2. The survival function is nonnegative, its value at 1 is at least 0.2731, and its value at 1/2 is at most 0.467. Hence S(1)≥0.2731>0.2186>0.467²≥S(1/2)², contrary to NBU. This refutes the universal assertion in Question 8. It does not classify the other positive parameters or the source’s other questions. The second-moment obstruction and the remaining range are discussed separately in the problem dossier.

## References

- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.besselK`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.bessel_mix`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.claim`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.density`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.density_one`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.err`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.exp_lower_cert`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.exp_scaled_bounds`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.exp_upper_cert`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.grid_integral_lower`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.grid_integral_upper`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.kernel`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.kernel_dec`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.kernel_inc`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.kernel_integrable`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.kernel_lower`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert0`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert104`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert112`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert120`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert128`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert136`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert144`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert152`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert16`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert160`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert168`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert176`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert184`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert192`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert24`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert32`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert40`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert48`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert56`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert64`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert72`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert8`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert80`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert88`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerCert96`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerData`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum0`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum104`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum112`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum120`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum128`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum136`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum144`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum152`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum16`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum160`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum168`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum176`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum184`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum192`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum24`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum32`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum40`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum48`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum56`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum64`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum72`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum8`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum80`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum88`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerSum96`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lowerY`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lower_cell`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lower_certificate`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.lower_sum`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.mix_integrable_inner`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.mix_integral_inner`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.peak_upper`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.poly`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.result`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.survival`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.survival_mix`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert0`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert16`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert24`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert32`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert40`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert48`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert56`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert64`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert72`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert8`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert80`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperCert88`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperData`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upperY`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upper_cell`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.upper_certificate`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.witness_lower`
- Truth anchor: `D5/S3/Analytic/GammaGammaNBU/Result.witness_upper`
