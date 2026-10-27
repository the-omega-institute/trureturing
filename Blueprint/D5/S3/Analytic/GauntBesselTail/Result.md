# Gaunt's weighted Bessel tail inequality

## Abstract

Squared-order convexity and an exact integral identity give the sharp weighted Bessel tail bound.

**Definition 1.1 (alpha).**

$$\forall nu \in \mathbb {R},\; \forall n \in \mathbb {R},\; \operatorname {alpha}\left(nu, n\right) = nu + n - \operatorname {Real.sqrt}\left((nu + n)^{2} - 2 \cdot nu - 1\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.alpha` (`✓ std3`).

*Citation.* Robert E. Gaunt (2019). *Inequalities for some integrals involving modified Bessel functions*. DOI: [10.1090/proc/14433](https://doi.org/10.1090/proc/14433). URL: <https://arxiv.org/abs/1806.00524>.

*Commentary.*

The smaller parameter shift in Conjecture 2.4.

**Definition 1.2 (alphaPrime).**

$$\forall nu \in \mathbb {R},\; \forall n \in \mathbb {R},\; \operatorname {alphaPrime}\left(nu, n\right) = nu + n + \operatorname {Real.sqrt}\left((nu + n)^{2} - 2 \cdot nu - 1\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.alphaPrime` (`✓ std3`).

*Citation.* Robert E. Gaunt (2019). *Inequalities for some integrals involving modified Bessel functions*. DOI: [10.1090/proc/14433](https://doi.org/10.1090/proc/14433). URL: <https://arxiv.org/abs/1806.00524>.

*Commentary.*

The second shift gives the opposite Bessel order.

**Definition 1.3 (tail).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall x \in \mathbb {R},\; \operatorname {tail}\left(nu, p, x\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(x\right)\right), t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(p, t\right)\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.tail` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2026). *Modified Bessel functions, integral representations*. DOI: [10.18434/T4J30S](https://doi.org/10.18434/T4J30S). URL: <https://dlmf.nist.gov/10.32.E9>.

*Commentary.*

The real power is used on the positive integration domain. The reused Bessel integral is DLMF 10.32.9.

**Definition 1.4 (The complete sharp tail assertion).**

$$claim = \left((\forall n \in \mathbb {R},\; \forall nu \in \mathbb {R},\; ((n < 1) \land (1 - n + \operatorname {Real.sqrt}\left(2 \cdot \left(1 - n\right)\right) \le nu)) \Rightarrow (\forall x \in \mathbb {R},\; (0 < x) \Rightarrow ((x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu + n - \operatorname {alpha}\left(nu, n\right), x\right) < \operatorname {tail}\left(nu, nu + n, x\right)))) \land ((\forall n \in \mathbb {R},\; \forall nu \in \mathbb {R},\; ((n < 1) \land (1 - n + \operatorname {Real.sqrt}\left(2 \cdot \left(1 - n\right)\right) \le nu)) \Rightarrow (\forall beta \in \mathbb {R},\; ((beta \ne \operatorname {alpha}\left(nu, n\right)) \land (beta \ne \operatorname {alphaPrime}\left(nu, n\right))) \Rightarrow ((\forall x \in \mathbb {R},\; (0 < x) \Rightarrow ((x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu + n - beta, x\right) < (x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu + n - \operatorname {alpha}\left(nu, n\right), x\right))) \lor (\exists y \in \mathbb {R},\; (0 < y) \land (\operatorname {tail}\left(nu, nu + n, y\right) < (y)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu + n - beta, y\right)))))) \land (\forall nu \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow (\operatorname {tail}\left(nu, nu + 1, x\right) = (x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu, x\right))))\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.claim` (`✓ std3`).

*Citation.* Robert E. Gaunt (2019). *Inequalities for some integrals involving modified Bessel functions*. DOI: [10.1090/proc/14433](https://doi.org/10.1090/proc/14433). URL: <https://arxiv.org/abs/1806.00524>.

*Commentary.*

“Conjecture 2.4. Let n < 1. For ν ≥ 1 − n + √(2(1 − n)), define α_{ν,n} := ν + n − √((ν + n)² − 2ν − 1). Then, for all x > 0, ∫_x^∞ K_{ν+n}(t)/t^ν dt > K_{ν+n−α_{ν,n}}(x)/x^ν, ν ≥ 1 − n + √(2(1 − n)). (2.17) We have equality in (2.17) when n = 1, and this equality is valid for all ν ∈ ℝ. Let α′_{ν,n} := ν + n + √((ν + n)² − 2ν − 1), so that ν + n − α′_{ν,n} = −(ν + n − α_{ν,n}) and thus K_{ν+n−α′_{ν,n}}(x) = K_{ν+n−α_{ν,n}}(x). Then, the index ν + n − α_{ν,n} (and equivalently ν + n − α′_{ν,n}) in inequality (2.17) is best possible, in the sense that, for any β ∉ {α_{ν,n}, α′_{ν,n}}, either K_{ν+n−β}(x)/x^ν < K_{ν+n−α_{ν,n}}(x)/x^ν for all x > 0, or there exists a y > 0 such that ∫_y^∞ K_{ν+n}(t)/t^ν dt < K_{ν+n−β}(y)/y^ν.” Lean uses the displayed definitions and formulas above to encode this statement; the reused K is exactly the positive-argument integral representation in DLMF 10.32.9, and the tail uses t^(−ν) on t>x>0.

**Theorem 1.5 (sinh gap pos).**

$$\forall v \in \mathbb {R},\; (0 < v) \Rightarrow (0 < v \cdot \operatorname {Real.cosh}\left(v\right) - \operatorname {Real.sinh}\left(v\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.sinh_gap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative is v sinh(v), strictly positive for v>0. This proves squared-order convexity.

**Theorem 1.6 (cosh sqrt deriv).**

$$\forall u \in \mathbb {R},\; \forall s \in \mathbb {R},\; (0 < s) \Rightarrow (\operatorname {HasDerivAt}\left(s: \mathbb {R}\mapsto \operatorname {Real.cosh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right), \frac{u}{2 \cdot \operatorname {Real.sqrt}\left(s\right)} \cdot \operatorname {Real.sinh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right), s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chain rule differentiates the squared-order kernel away from s=0.

**Theorem 1.7 (cosh sqrt deriv2).**

$$\forall u \in \mathbb {R},\; \forall s \in \mathbb {R},\; (0 < s) \Rightarrow (\operatorname {HasDerivAt}\left(s: \mathbb {R}\mapsto \frac{u}{2 \cdot \operatorname {Real.sqrt}\left(s\right)} \cdot \operatorname {Real.sinh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right), \frac{u}{4 \cdot (\operatorname {Real.sqrt}\left(s\right))^{3}} \cdot \left(u \cdot \operatorname {Real.sqrt}\left(s\right) \cdot \operatorname {Real.cosh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right) - \operatorname {Real.sinh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right)\right), s\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_deriv2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A second differentiation exposes the positive hyperbolic gap.

**Theorem 1.8 (squared order strictConvex).**

$$\forall u \in \mathbb {R},\; (0 < u) \Rightarrow (\operatorname {StrictConvexOn}\left(\mathbb {R}, \operatorname {Set.Ici}\left(0\right), s: \mathbb {R}\mapsto \operatorname {Real.cosh}\left(u \cdot \operatorname {Real.sqrt}\left(s\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.squared_order_strictConvex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity at zero and positivity of the second derivative prove strict convexity on the closed nonnegative half-line.

**Theorem 1.9 (cosh sqrt sq).**

$$\forall u \in \mathbb {R},\; \forall a \in \mathbb {R},\; (0 \le u) \Rightarrow (\operatorname {Real.cosh}\left(u \cdot \operatorname {Real.sqrt}\left((a)^{2}\right)\right) = \operatorname {Real.cosh}\left(a \cdot u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evenness removes the absolute value of the order.

**Theorem 1.10 (positive order kernel).**

$$\forall u \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall q \in \mathbb {R},\; \forall nu \in \mathbb {R},\; (0 < u) \Rightarrow ((0 < q) \Rightarrow ((q < nu) \Rightarrow (((p)^{2} = (q)^{2} + 2 \cdot nu + 1) \Rightarrow (\operatorname {Real.cosh}\left(q \cdot u\right) \cdot \operatorname {Real.cosh}\left(u\right) + \frac{nu}{q} \cdot \operatorname {Real.sinh}\left(q \cdot u\right) \cdot \operatorname {Real.sinh}\left(u\right) < \operatorname {Real.cosh}\left(p \cdot u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.positive_order_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compare adjacent secant slopes at (q−1)², (q+1)² and p². Hyperbolic addition then gives the sharp strict kernel inequality.

**Theorem 1.11 (zero order kernel).**

$$\forall u \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall nu \in \mathbb {R},\; (0 < u) \Rightarrow ((0 < nu) \Rightarrow (((p)^{2} = 2 \cdot nu + 1) \Rightarrow (\operatorname {Real.cosh}\left(u\right) + nu \cdot u \cdot \operatorname {Real.sinh}\left(u\right) < \operatorname {Real.cosh}\left(p \cdot u\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.zero_order_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q=0 use the tangent at s=1 instead of the two distinct secants.

**Theorem 1.12 (parameters).**

$$\forall nu \in \mathbb {R},\; \forall n \in \mathbb {R},\; (n < 1) \Rightarrow ((1 - n + \operatorname {Real.sqrt}\left(2 \cdot \left(1 - n\right)\right) \le nu) \Rightarrow ((0 \le (nu + n)^{2} - 2 \cdot nu - 1) \land ((\operatorname {Real.sqrt}\left((nu + n)^{2} - 2 \cdot nu - 1\right) < nu) \land (\operatorname {Real.sqrt}\left((nu + n)^{2} - 2 \cdot nu - 1\right) + 1 < nu + n))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source parameter range gives a nonnegative discriminant, q<nu and q+1<nu+n.

**Theorem 1.13 (exponential kernel integrable).**

$$\forall z \in \mathbb {R},\; \forall A \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.Integrable}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-z \cdot \operatorname {Real.cosh}\left(u\right) + A \cdot u\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.exponential_kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tilted integrable Gaussian dominates the exponential kernel on the whole real line.

**Theorem 1.14 (bessel kernel integrable).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {Real.cosh}\left(r \cdot u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_kernel_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand cosh as a sum of exponentials and apply Gaussian domination for both signs of the order.

**Theorem 1.15 (bessel cosh integrable).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {Real.cosh}\left(u\right) \cdot \operatorname {Real.cosh}\left(r \cdot u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_cosh_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product of the two coshes is the half-sum of the adjacent-order coshes.

**Theorem 1.16 (bessel hasDerivAt).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {HasDerivAt}\left(\operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r\right), -\operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {Real.cosh}\left(u\right) \cdot \operatorname {Real.cosh}\left(r \cdot u\right)\right), z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local domination with argument z/2 justifies differentiation under the integral.

**Theorem 1.17 (integral decay).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; (\forall u \in \mathbb {R},\; (0 < u) \Rightarrow (0 \le \operatorname {f}\left(u\right))) \Rightarrow ((\forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {f}\left(u\right), \operatorname {Set.Ioi}\left(0\right)\right))) \Rightarrow (\forall t \in \mathbb {R},\; (1 \le t) \Rightarrow (\operatorname {abs}\left(\operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(t \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {f}\left(u\right)\right)\right) \le \operatorname {Real.exp}\left(\frac{-t}{2}\right) \cdot \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(\frac{1}{2} \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {f}\left(u\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.integral_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t≥1, cosh(u)≥1 splits off a uniform exp(−t/2) factor.

**Theorem 1.18 (bessel bigO).**

$$\forall r \in \mathbb {R},\; \operatorname {Asymptotics.IsBigO}\left(\operatorname {Filter.atTop}\left(\right), \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r\right), t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\frac{t}{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_bigO` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive Bessel kernel inherits the uniform exponential decay.

**Theorem 1.19 (weighted decay).**

$$\forall F \in \mathbb {R} \to \mathbb {R},\; (\operatorname {ContinuousOn}\left(F, \operatorname {Set.Ioi}\left(0\right)\right)) \Rightarrow ((\operatorname {Asymptotics.IsBigO}\left(\operatorname {Filter.atTop}\left(\right), F, t: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\frac{t}{2}\right)\right)) \Rightarrow (\forall nu \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow ((\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {F}\left(t\right), \operatorname {Set.Ioi}\left(x\right)\right)) \land (\operatorname {Filter.Tendsto}\left(t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {F}\left(t\right), \operatorname {Filter.atTop}\left(\right), \operatorname {nhds}\left(0\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.weighted_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any real power times the exponentially decreasing function is integrable on every positive tail and tends to zero.

**Theorem 1.20 (tail integrable).**

$$\forall nu \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, t\right), \operatorname {Set.Ioi}\left(x\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.tail_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted Bessel kernel satisfies the hypotheses of weighted_decay.

**Theorem 1.21 (weighted bessel tendsto).**

$$\forall nu \in \mathbb {R},\; \forall r \in \mathbb {R},\; \operatorname {Filter.Tendsto}\left(t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, t\right), \operatorname {Filter.atTop}\left(\right), \operatorname {nhds}\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.weighted_bessel_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weighted Bessel function vanishes at positive infinity.

**Theorem 1.22 (abs sinh le cosh).**

$$\forall u \in \mathbb {R},\; \operatorname {abs}\left(\operatorname {Real.sinh}\left(u\right)\right) \le \operatorname {Real.cosh}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.abs_sinh_le_cosh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply sinh(u)<cosh(u) at u and −u. This bounds the integration-by-parts kernel.

**Theorem 1.23 (bessel sinh integrable).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {Real.sinh}\left(r \cdot u\right) \cdot \operatorname {Real.sinh}\left(u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_sinh_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute sinh product is bounded by the integrable cosh product.

**Theorem 1.24 (exponential kernel tendsto).**

$$\forall z \in \mathbb {R},\; \forall A \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {Filter.Tendsto}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-z \cdot \operatorname {Real.cosh}\left(u\right) + A \cdot u\right), \operatorname {Filter.atTop}\left(\right), \operatorname {nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.exponential_kernel_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same quadratic domination also proves pointwise decay at infinity.

**Theorem 1.25 (u exponential integrable).**

$$\forall z \in \mathbb {R},\; \forall A \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto u \cdot \operatorname {Real.exp}\left(-z \cdot \operatorname {Real.cosh}\left(u\right) + A \cdot u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.u_exponential_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The elementary bound u≤exp(u) absorbs the extra positive-domain factor.

**Theorem 1.26 (u exponential tendsto).**

$$\forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {Filter.Tendsto}\left(u: \mathbb {R}\mapsto u \cdot \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right), \operatorname {Filter.atTop}\left(\right), \operatorname {nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.u_exponential_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absorb u into exp(u) and use the exponential-kernel limit.

**Definition 1.27 (S).**

$$\forall r \in \mathbb {R},\; \forall u \in \mathbb {R},\; \operatorname {S}\left(r, u\right) = \operatorname {ite}\left(r = 0, u, \frac{\operatorname {Real.sinh}\left(r \cdot u\right)}{r}\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This continuous-order antiderivative treats r=0 separately.

**Theorem 1.28 (S deriv).**

$$\forall r \in \mathbb {R},\; \forall u \in \mathbb {R},\; \operatorname {HasDerivAt}\left(\operatorname {S}\left(r\right), \operatorname {Real.cosh}\left(r \cdot u\right), u\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.S_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real r, the derivative in u of S_r is cosh(ru).

**Theorem 1.29 (S sinh integrable).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {S}\left(r, u\right) \cdot \operatorname {Real.sinh}\left(u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.S_sinh_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero-order case follows from the sinh-product bound; the zero-order case uses the extra-u envelope.

**Theorem 1.30 (S kernel tendsto).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {Filter.Tendsto}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {S}\left(r, u\right), \operatorname {Filter.atTop}\left(\right), \operatorname {nhds}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.S_kernel_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The boundary term in the hyperbolic integration by parts tends to zero.

**Theorem 1.31 (bessel ibp).**

$$\forall r \in \mathbb {R},\; \forall z \in \mathbb {R},\; (0 < z) \Rightarrow (\operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, z\right) = z \cdot \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(z \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {S}\left(r, u\right) \cdot \operatorname {Real.sinh}\left(u\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_ibp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate exp(−z cosh u)S_r(u) and apply the fundamental theorem on the upper half-line.

**Definition 1.32 (H).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall u \in \mathbb {R},\; \operatorname {H}\left(nu, p, r, u\right) = \operatorname {Real.cosh}\left(p \cdot u\right) - \operatorname {Real.cosh}\left(r \cdot u\right) \cdot \operatorname {Real.cosh}\left(u\right) - nu \cdot \operatorname {S}\left(r, u\right) \cdot \operatorname {Real.sinh}\left(u\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed kernel measures the difference between the tail and its proposed lower expression.

**Definition 1.33 (J).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall t \in \mathbb {R},\; \operatorname {J}\left(nu, p, r, t\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(t \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {H}\left(nu, p, r, u\right)\right)$$

*Formalization.* `D5/S3/Analytic/GauntBesselTail/Result.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J is the Laplace integral of the signed kernel.

**Theorem 1.34 (H integrable).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall t \in \mathbb {R},\; (0 < t) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(t \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {H}\left(nu, p, r, u\right), \operatorname {Set.Ioi}\left(0\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.H_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each of the three terms is absolutely integrable.

**Theorem 1.35 (J eq).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall t \in \mathbb {R},\; (0 < t) \Rightarrow (\operatorname {J}\left(nu, p, r, t\right) = \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(p, t\right) - \frac{\operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r + 1, t\right) + \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r - 1, t\right)}{2} - \frac{nu}{t} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.J_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The adjacent-order identity and integration by parts express J using ordinary Bessel functions.

**Theorem 1.36 (weighted J integrable).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {J}\left(nu, p, r, t\right), \operatorname {Set.Ioi}\left(x\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.weighted_J_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

J_eq reduces this integrability to three weighted Bessel tails and one adjacent real power.

**Theorem 1.37 (tail identity).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall r \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow (\operatorname {tail}\left(nu, p, x\right) - (x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, x\right) = \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(x\right)\right), t: \mathbb {R}\mapsto (t)^{-nu} \cdot \operatorname {J}\left(nu, p, r, t\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.tail_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiate x^(−nu)K_r(x), integrate its derivative on the positive upper half-line, and use its zero limit.

**Theorem 1.38 (integral Ioi pos).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; \forall a \in \mathbb {R},\; (\operatorname {MeasureTheory.IntegrableOn}\left(f, \operatorname {Set.Ioi}\left(a\right)\right)) \Rightarrow ((\forall u \in \mathbb {R},\; (a < u) \Rightarrow (0 < \operatorname {f}\left(u\right))) \Rightarrow (0 < \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(a\right)\right), u: \mathbb {R}\mapsto \operatorname {f}\left(u\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.integral_Ioi_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive integrand on an upper half-line has support of positive Lebesgue measure.

**Theorem 1.39 (strict tail).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall q \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 \le q) \Rightarrow ((q < nu) \Rightarrow (((p)^{2} = (q)^{2} + 2 \cdot nu + 1) \Rightarrow ((0 < x) \Rightarrow ((x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(q, x\right) < \operatorname {tail}\left(nu, p, x\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.strict_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict scalar kernel comparison makes J positive, and tail_identity then gives the strict bound.

**Theorem 1.40 (n one identity).**

$$\forall nu \in \mathbb {R},\; \forall x \in \mathbb {R},\; (0 < x) \Rightarrow (\operatorname {tail}\left(nu, nu + 1, x\right) = (x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(nu, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.n_one_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The addition formula makes H identically zero when p=nu+1 and r=nu, including nu=0 and negative nu.

**Theorem 1.41 (laplace negative).**

$$\forall f \in \mathbb {R} \to \mathbb {R},\; (\forall t \in \mathbb {R},\; (0 < t) \Rightarrow (\operatorname {MeasureTheory.IntegrableOn}\left(u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(t \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {f}\left(u\right), \operatorname {Set.Ioi}\left(0\right)\right))) \Rightarrow (\forall delta \in \mathbb {R},\; (0 < delta) \Rightarrow ((\forall u \in \mathbb {R},\; (0 < u) \Rightarrow ((u < delta) \Rightarrow (\operatorname {f}\left(u\right) < 0))) \Rightarrow (\operatorname {Filter.Eventually}\left(t: \mathbb {R}\mapsto \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}\left(\right), \operatorname {Set.Ioi}\left(0\right)\right), u: \mathbb {R}\mapsto \operatorname {Real.exp}\left(-\left(t \cdot \operatorname {Real.cosh}\left(u\right)\right)\right) \cdot \operatorname {f}\left(u\right)\right) < 0, \operatorname {Filter.atTop}\left(\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.laplace_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A negative interval next to the origin contributes at a slower exponential decay rate than the outer positive part. A fixed inner subinterval therefore forces a negative Laplace integral for every sufficiently large t.

**Theorem 1.42 (H negative near).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall q \in \mathbb {R},\; \forall r \in \mathbb {R},\; (0 \le q) \Rightarrow ((q < r) \Rightarrow (((p)^{2} = (q)^{2} + 2 \cdot nu + 1) \Rightarrow (\exists delta \in \mathbb {R},\; (0 < delta) \land (\forall u \in \mathbb {R},\; (0 < u) \Rightarrow ((u < delta) \Rightarrow (\operatorname {H}\left(nu, p, r, u\right) < 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.H_negative_near` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero both H and its first derivative vanish, while its second derivative is q²−r²<0. The derivative test gives a negative right-hand interval.

**Theorem 1.43 (larger order failure).**

$$\forall nu \in \mathbb {R},\; \forall p \in \mathbb {R},\; \forall q \in \mathbb {R},\; \forall r \in \mathbb {R},\; (0 \le q) \Rightarrow ((q < r) \Rightarrow (((p)^{2} = (q)^{2} + 2 \cdot nu + 1) \Rightarrow (\operatorname {Filter.Eventually}\left(x: \mathbb {R}\mapsto \operatorname {tail}\left(nu, p, x\right) < (x)^{-nu} \cdot \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(r, x\right), \operatorname {Filter.atTop}\left(\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.larger_order_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The local kernel sign and laplace_negative make J negative for all sufficiently large t. The tail identity proves failure at every sufficiently large x, stronger than a single positive witness.

**Theorem 1.44 (bessel order lt).**

$$\forall a \in \mathbb {R},\; \forall b \in \mathbb {R},\; \forall x \in \mathbb {R},\; (\operatorname {abs}\left(a\right) < \operatorname {abs}\left(b\right)) \Rightarrow ((0 < x) \Rightarrow (\operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(a, x\right) < \operatorname {D5.S3.Analytic.GammaGammaNBU.Result.besselK}\left(b, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.bessel_order_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict increase of cosh in the absolute order and positive integration prove strict order monotonicity.

**Theorem 1.45 (The sharp bound and its optimality).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GauntBesselTail/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/gaunt-2019-bessel-tail-conjecture` (proved) by `D5/S3/Analytic/GauntBesselTail/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gaunt-2019-bessel-tail-conjecture","declaration_gid":"D5/S3/Analytic/GauntBesselTail/Result.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Robert E. Gaunt (2019). *Inequalities for some integrals involving modified Bessel functions*. DOI: [10.1090/proc/14433](https://doi.org/10.1090/proc/14433). URL: <https://arxiv.org/abs/1806.00524>.

*Commentary.*

The strict bound follows from squared-order convexity and the exact tail identity. A smaller absolute order gives a strictly smaller right side at every positive x; a larger absolute order fails for all sufficiently large x. The two excluded shifts give opposite orders and therefore identical Bessel values. When n=1, the hyperbolic addition formula makes the signed kernel identically zero for every real nu.

## References

- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.H`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.H_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.H_negative_near`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.J`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.J_eq`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.S`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.S_deriv`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.S_kernel_tendsto`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.S_sinh_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.abs_sinh_le_cosh`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.alpha`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.alphaPrime`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_bigO`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_cosh_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_hasDerivAt`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_ibp`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_kernel_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_order_lt`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.bessel_sinh_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.claim`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_deriv`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_deriv2`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.cosh_sqrt_sq`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.exponential_kernel_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.exponential_kernel_tendsto`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.integral_Ioi_pos`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.integral_decay`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.laplace_negative`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.larger_order_failure`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.n_one_identity`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.parameters`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.positive_order_kernel`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.result`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.sinh_gap_pos`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.squared_order_strictConvex`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.strict_tail`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.tail`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.tail_identity`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.tail_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.u_exponential_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.u_exponential_tendsto`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.weighted_J_integrable`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.weighted_bessel_tendsto`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.weighted_decay`
- Truth anchor: `D5/S3/Analytic/GauntBesselTail/Result.zero_order_kernel`
- Dependency: [D5/S3/Analytic/GammaGammaNBU/Result](../GammaGammaNBU/Result.md)
- Dependency: [D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel](../../TotalVariation/Asymptotics/GaussianCoshKernel.md)
