# A modified Bessel ratio need not be log-concave

## Abstract

A positive rational series disproves log-concavity of a modified Bessel ratio.

**Definition 1.1 (The modified Bessel function of the first kind).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; \operatorname {besselI}\left(nu, z\right) = \sum '_{k: \mathbb {N}} \frac{(\frac{z}{2})^{2 \cdot k + nu}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + nu + 1\right)}$$

*Formalization.* `D5/S3/Analytic/BesselRatioLogConcavity/Result.besselI` (`✓ std3`).

*Citation.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Printed page 11 of arXiv:2408.01755v2 states: “Using the standard power series expansion of Iν [28, p.217] we have”. The following is its displayed ratio expansion, quoted verbatim from the supplied text extraction with the line order and detached superscripts retained:

“P∞ 2k 2k k

Iν1 (a1 x)

k=0 a1 x /[4 k!Γ(k + ν1 + 1)]

2 ν1 −ν2

P

.

= 2ν2 −ν2 aν11 a−ν

x

∞

2

2k 2k

k

Iν2 (a2 x)

k=0 a2 x /[4 k!Γ(k + ν2 + 1)]”

The extracted prefactor has detached superscripts; the normalization correspondence here is derived independently from the defining series, not asserted as a verbatim standalone formula in the paper. Factoring (a*x/2)^nu from each sum leaves terms a^(2k)*x^(2k)/(4^k*k!*Gamma(k+nu+1)); the ratio prefactor is 2^(nu2−nu1)*a1^nu1*a2^(−nu2)*x^(nu1−nu2). For equal orders the x powers cancel, and scales 1 and 2 leave 2^(−nu). The Lean definition uses the real series with the natural number 2k coerced to a real exponent. It is summable for z>0 and nu>−1.

**Definition 1.2 (The positive-order log-concavity clause).**

$$claim = \left(\forall nu1 \in \mathbb {R},\; \forall nu2 \in \mathbb {R},\; \forall a1 \in \mathbb {R},\; \forall a2 \in \mathbb {R},\; 0 < nu2 \Rightarrow \left(nu2 \le nu1 \Rightarrow \left(0 < a1 \Rightarrow \left(a1 \le a2 \Rightarrow \operatorname {ConcaveOn}\left(\mathbb {R}, \operatorname {Set.Ioi}\left(0\right), x: \mathbb {R}\mapsto \operatorname {Real.log}\left(\frac{\operatorname {besselI}\left(nu1, a1 \cdot x\right)}{\operatorname {besselI}\left(nu2, a2 \cdot x\right)}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/BesselRatioLogConcavity/Result.claim` (`✓ std3`).

*Citation.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Conjecture 1, printed page 12, with line breaks joined: “Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.”

The claim quantifies over all real orders nu1≥nu2>0 and all scales 0<a1≤a2. It states concavity on the entire positive real half-line of the logarithm of the standard modified Bessel ratio. Positivity of the series on this domain makes that the usual log-concavity assertion. The parameter b in the source does not occur in the ratio. Its unimodality clause is a separate assertion.

**Theorem 1.3 (Nonnegative terms).**

$$\forall nu \in \mathbb {R},\; \forall w \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 \le w \Rightarrow \left(\forall k \in \mathbb {N},\; 0 \le \operatorname {term}\left(nu, w, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative power divided by the positive factorial and rising factorial is nonnegative.

**Theorem 1.4 (The coefficient correspondence).**

$$\forall nu \in \mathbb {R},\; \forall w \in \mathbb {R},\; \forall k \in \mathbb {N},\; \operatorname {term}\left(nu, w, k\right) = \operatorname {D5.S3.Analytic.BesselRedheffer.Series.coeff}\left(nu + 1, k\right) \cdot (w)^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_eq_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here term(nu,w,k)=w^k/(k!*(nu+1)_k). It equals the normalized coefficient of lower parameter nu+1 multiplied by w^k, so the coefficient recurrence and absolute convergence apply.

**Theorem 1.5 (The weighted recurrence).**

$$\forall nu \in \mathbb {R},\; -1 < nu \Rightarrow \left(\forall w \in \mathbb {R},\; \forall k \in \mathbb {N},\; \operatorname {term}\left(nu, w, k + 1\right) = \frac{w}{\left(k + 1\right) \cdot \left(nu + 1 + k\right)} \cdot \operatorname {term}\left(nu, w, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the coefficient recurrence by w^(k+1) gives this recurrence for the weighted term.

**Theorem 1.6 (Convergence of the weighted series).**

$$\forall nu \in \mathbb {R},\; -1 < nu \Rightarrow \left(\forall w \in \mathbb {R},\; \operatorname {Summable}\left(k: \mathbb {N}\mapsto \operatorname {term}\left(nu, w, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The absolute convergence of the normalized coefficient series at lower parameter nu+1 supplies convergence for every real w.

**Theorem 1.7 (Gamma normalization of a summand).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 < z \Rightarrow \left(\forall k \in \mathbb {N},\; \frac{(\frac{z}{2})^{2 \cdot k + nu}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + nu + 1\right)} = \frac{(\frac{z}{2})^{nu}}{\operatorname {Real.Gamma}\left(nu + 1\right)} \cdot \operatorname {term}\left(nu, \frac{(z)^{2}}{4}, k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_term_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Gamma–Pochhammer identity and positive-base real-power identities separate the order-dependent normalization from each summand.

**Theorem 1.8 (Convergence of the modified Bessel series).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 < z \Rightarrow \operatorname {Summable}\left(k: \mathbb {N}\mapsto \frac{(\frac{z}{2})^{2 \cdot k + nu}}{\operatorname {Nat.factorial}\left(k\right) \cdot \operatorname {Real.Gamma}\left(k + nu + 1\right)}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After the summand identity, convergence follows by multiplying the normalized summable series by the fixed normalization factor.

**Theorem 1.9 (The normalized modified Bessel series).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 < z \Rightarrow \operatorname {besselI}\left(nu, z\right) = \frac{(\frac{z}{2})^{nu}}{\operatorname {Real.Gamma}\left(nu + 1\right)} \cdot \sum '_{k: \mathbb {N}} \operatorname {term}\left(nu, \frac{(z)^{2}}{4}, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the summand identity pulls the normalization factor outside the infinite sum.

**Theorem 1.10 (Positive certificate series).**

$$\forall w \in \mathbb {R},\; 0 \le w \Rightarrow 0 < \operatorname {series}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The function series(w) is the sum of term(1/10,w,k) over all natural k. Its constant term is one and all other terms are nonnegative.

**Theorem 1.11 (Rational terms and real terms).**

$$\forall w \in \mathbb {Q},\; \forall k \in \mathbb {N},\; \operatorname {term}\left(\frac{1}{10}, w, k\right) = \operatorname {qterm}\left(w, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational recurrence qterm(w,0)=1 and qterm(w,k+1)=w/((k+1)*(11/10+k))*qterm(w,k) agrees with the real term. Rational arguments and values in this formula are coerced to real values where required.

**Theorem 1.12 (The partial sum is a lower bound).**

$$\forall w \in \mathbb {Q},\; 0 \le w \Rightarrow \operatorname {qlower}\left(w\right) \le \operatorname {series}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational number qlower(w) sums qterm(w,k) over 0<=k<60. Nonnegative remaining terms make this a lower bound; qlower and w are coerced to real values in the comparison.

**Theorem 1.13 (A bound on the tail ratio).**

$$\forall w \in \mathbb {Q},\; 0 \le w \Rightarrow \left(\forall k \in \mathbb {N},\; 60 \le k \Rightarrow \operatorname {term}\left(\frac{1}{10}, w, k + 1\right) \le \operatorname {qratio}\left(w\right) \cdot \operatorname {term}\left(\frac{1}{10}, w, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.tail_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational number qratio(w) is w/(61*(611/10)). For k>=60 the recurrence denominator is at least 61*(611/10), giving the displayed comparison after coercion to real values.

**Theorem 1.14 (The geometric upper bound).**

$$\forall w \in \mathbb {Q},\; 0 \le w \Rightarrow \left(\operatorname {qratio}\left(w\right) < 1 \Rightarrow \operatorname {series}\left(w\right) \le \operatorname {qupper}\left(w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rational number qupper(w) is qlower(w)+qterm(w,60)/(1−qratio(w)). A geometric majorant for the tail starting at index 60 bounds the real series by this rational value coerced to the reals.

**Theorem 1.15 (Cancellation of the common normalization).**

$$\forall nu \in \mathbb {R},\; \forall t \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 < t \Rightarrow \frac{\operatorname {besselI}\left(nu, t\right)}{\operatorname {besselI}\left(nu, 2 \cdot t\right)} = (2)^{-nu} \cdot \frac{\sum '_{k: \mathbb {N}} \operatorname {term}\left(nu, \frac{(t)^{2}}{4}, k\right)}{\sum '_{k: \mathbb {N}} \operatorname {term}\left(nu, (t)^{2}, k\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive power and Gamma factors cancel in the ratio, leaving the common factor 2^(−nu) and a quotient of normalized series.

**Theorem 1.16 (Positivity on the positive half-line).**

$$\forall nu \in \mathbb {R},\; \forall z \in \mathbb {R},\; -1 < nu \Rightarrow \left(0 < z \Rightarrow 0 < \operatorname {besselI}\left(nu, z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive argument and order greater than −1 every summand is positive; convergence and the term of index zero give a positive sum.

**Theorem 1.17 (Six exact rational bounds).**

$$\frac{1584}{1000} \le \operatorname {qlower}\left(\frac{9}{16}\right) \land \left(\frac{223368}{1000} \le \operatorname {qlower}\left(\frac{225}{16}\right) \land \left(\frac{894574}{1000} \le \operatorname {qlower}\left(\frac{81}{4}\right) \land \left(\operatorname {qupper}\left(\frac{81}{16}\right) \le \frac{15316}{1000} \land \left(\operatorname {qupper}\left(\frac{9}{4}\right) \le \frac{4447}{1000} \land \operatorname {qupper}\left(\frac{225}{4}\right) \le 264068\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.numeric_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All six comparisons are inequalities in the rationals, evaluated with the 60-term partial sums and the geometric upper bounds.

**Theorem 1.18 (The strict series-product comparison).**

$$(\operatorname {series}\left(\frac{81}{16}\right))^{2} \cdot \operatorname {series}\left(\frac{9}{4}\right) \cdot \operatorname {series}\left(\frac{225}{4}\right) < \operatorname {series}\left(\frac{9}{16}\right) \cdot \operatorname {series}\left(\frac{225}{16}\right) \cdot (\operatorname {series}\left(\frac{81}{4}\right))^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three lower bounds and three upper bounds imply the strict product comparison; every series factor used in multiplying the inequalities is positive.

**Theorem 1.19 (The midpoint inequality is reversed).**

$$(\frac{\operatorname {besselI}\left(\frac{1}{10}, \frac{9}{2}\right)}{\operatorname {besselI}\left(\frac{1}{10}, 9\right)})^{2} < \frac{\operatorname {besselI}\left(\frac{1}{10}, \frac{3}{2}\right)}{\operatorname {besselI}\left(\frac{1}{10}, 3\right)} \cdot \frac{\operatorname {besselI}\left(\frac{1}{10}, \frac{15}{2}\right)}{\operatorname {besselI}\left(\frac{1}{10}, 15\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At order 1/10 the ratio at 9/2 squared is smaller than the product of the ratios at 3/2 and 15/2. Positivity permits logarithms, giving the failure of midpoint concavity.

**Theorem 1.20 (An exact infinite-series counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRatioLogConcavity/Result.result` (`✓ std3`). ∎

*Resolves.* `Problems/karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity` (refuted) by `D5/S3/Analytic/BesselRatioLogConcavity/Result.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity","declaration_gid":"D5/S3/Analytic/BesselRatioLogConcavity/Result.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Karp, A. Vishnyakova, and Y. Zhang (2025). *Unimodality preservation by ratios of functional series and integral transforms*. DOI: [10.1007/s00025-025-02431-4](https://doi.org/10.1007/s00025-025-02431-4). URL: <https://arxiv.org/abs/2408.01755>.

*Commentary.*

Take equal orders nu1=nu2=1/10 and scales a1=1,a2=2. Write S(w)=∑ₖ₌₀∞ w^k/(k! (11/10)ₖ). The Gamma–Pochhammer identity gamma_pochhammer gives Iν(t)/Iν(2t)=2^(−ν) S(t²/4)/S(t²). Gamma factors cancel, and the positive real power factor is common to all three points.

For a nonnegative rational w, let L(w) be the sum over 0≤k<60, let t60(w) be the term of index 60, and put rho(w)=w/(61·(611/10)). Every successive ratio starting at index 60 is at most rho(w). When rho(w)<1, the infinite series lies between L(w) and L(w)+t60(w)/(1−rho(w)). Exact rational arithmetic gives S(9/16)≥1.584, S(225/16)≥223.368 and S(81/4)≥894.574, while S(81/16)≤15.316, S(9/4)≤4.447 and S(225/4)≤264068.

These bounds imply S(9/16)S(225/16)S(81/4)²>S(81/16)²S(9/4)S(225/4). Thus R(3/2)R(15/2)>R(9/2)² for R(t)=I₁⁄₁₀(t)/I₁⁄₁₀(2t). Taking logarithms contradicts concavity at the midpoint 9/2. This disproves the universal log-concavity clause; it leaves unimodality and the full parameter range of log-concavity unresolved.

## References

- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.besselI`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_eq`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_pos`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_ratio`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_summable`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.bessel_term_eq`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.claim`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.numeric_certificate`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.result`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_lower`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_pos`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_product`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.series_upper`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.tail_ratio`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_cast`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_eq_coeff`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_nonneg`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_step`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.term_summable`
- Truth anchor: `D5/S3/Analytic/BesselRatioLogConcavity/Result.witness`
- Dependency: [D5/S3/Analytic/BesselRedheffer/Series](../BesselRedheffer/Series.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
