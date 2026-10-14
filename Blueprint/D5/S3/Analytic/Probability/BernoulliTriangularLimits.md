# Bernoulli Triangular Limits

## Abstract

Divergent Bernoulli row variances give central and local limits for polynomial coefficient laws.

**Definition 1.1 (rowMean).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{rowMean}\left(p\right) = \sum_{i: \operatorname{Fin}\left(m\right)} ((p\left(i\right): \mathbb{R}))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mean of the unshifted Bernoulli row.

**Definition 1.2 (rowVariance).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \operatorname{rowVariance}\left(p\right) = \sum_{i: \operatorname{Fin}\left(m\right)} ((p\left(i\right): \mathbb{R}) \cdot (1 - (p\left(i\right): \mathbb{R})))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowVariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the Bernoulli variances.

**Definition 1.3 (rowMass).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), \forall (k: \mathbb{Z}), \operatorname{rowMass}\left(p, k\right) = \sum_{x: \operatorname{Fin}\left(m\right) \to \operatorname{Bool}} (\operatorname{ite}\left(((\sum_{i: \operatorname{Fin}\left(m\right)} (\operatorname{Bool}.\operatorname{toNat}\left(x\left(i\right)\right)): \mathbb{N}): \mathbb{Z}) = k, \operatorname{bernoulliWeight}\left(p, x\right), 0\right))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer-lattice mass of the sum of Boolean coordinates. The full natural-number sum is cast to the integers.

**Theorem 1.4 (bernoulli_array_uniform_lattice_limit).**

$$\forall (m: \mathbb{N} \to \mathbb{N}), \forall (p: \forall (n: \mathbb{N}), \operatorname{Fin}\left(m\left(n\right)\right) \to \operatorname{unitInterval}), (\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rowVariance}\left(p\left(n\right)\right)), atTop, atTop\right)) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (k: \mathbb{Z}), \left|\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{rowVariance}\left(p\left(n\right)\right)\right) \cdot \operatorname{rowMass}\left(p\left(n\right), k\right) - \operatorname{gaussianPDFReal}\left(0, 1\right)\left(\frac{(k: \mathbb{R}) - \operatorname{rowMean}\left(p\left(n\right)\right)}{\operatorname{Real}.\operatorname{sqrt}\left(\operatorname{rowVariance}\left(p\left(n\right)\right)\right)}\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_array_uniform_lattice_limit` (`✓ std3`). ∎

*Citation.* Edward A. Bender (1973). *Central and local limit theorems applied to asymptotic enumeration*. DOI: [10.1016/0097-3165(73)90038-1](https://doi.org/10.1016/0097-3165(73)90038-1). URL: <https://doi.org/10.1016/0097-3165(73)90038-1>.

*Commentary.*

Fourier inversion and dominated convergence give a uniform local limit on the integer lattice. The sum of the Boolean coordinates is centered by rowMean.

**Theorem 1.5 (uniform_lattice_limit_to_floor).**

$$\forall (a: \mathbb{N} \to \left(\mathbb{Z} \to \mathbb{R}\right)), \forall (M: \mathbb{N} \to \mathbb{R}), \forall (S: \mathbb{N} \to \mathbb{R}), ((\operatorname{Tendsto}\left(S, atTop, atTop\right)) \land (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (k: \mathbb{Z}), \left|S\left(n\right) \cdot a\left(n, k\right) - \operatorname{gaussianPDFReal}\left(0, 1\right)\left(\frac{(k: \mathbb{R}) - M\left(n\right)}{S\left(n\right)}\right)\right| < e), atTop\right)))) \Rightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|S\left(n\right) \cdot a\left(n, \left\lfloor M\left(n\right) + t \cdot S\left(n\right)\right\rfloor\right) - \operatorname{gaussianPDFReal}\left(0, 1\right)\left(t\right)\right| < e), atTop\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.uniform_lattice_limit_to_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniform continuity of the Gaussian density transfers a uniform lattice limit to the literal integer floor of M(n)+t*S(n). The rounding error is less than 1/S(n).

**Definition 1.6 (mu).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \operatorname{mu}\left(f\right) = \frac{\operatorname{Polynomial}.\operatorname{eval}\left(1, \operatorname{derivative}\left(f\right)\right)}{\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right)}$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.mu` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Theorem 4.2, page 9, defines μₙ = fₙ′(1)/fₙ(1). The first logarithmic derivative of f evaluated at one is the coefficient-law mean.

**Definition 1.7 (sigmaSq).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \operatorname{sigmaSq}\left(f\right) = \frac{\operatorname{Polynomial}.\operatorname{eval}\left(1, \operatorname{derivative}\left(\operatorname{derivative}\left(f\right)\right)\right)}{\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right)} + \operatorname{mu}\left(f\right) - (\operatorname{mu}\left(f\right))^{2}$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Theorem 4.2, page 9, defines σₙ² = fₙ″(1)/fₙ(1) + μₙ − μₙ². The variance is the normalized second derivative at one plus the mean minus its square.

**Definition 1.8 (sigma).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \operatorname{sigma}\left(f\right) = \operatorname{Real}.\operatorname{sqrt}\left(\operatorname{sigmaSq}\left(f\right)\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigma` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

The standard deviation σₙ is the nonnegative square root of the variance in Section 4, pages 8–9. The encoding uses Real.sqrt sigmaSq.

**Definition 1.9 (prob).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \forall (k: \mathbb{Z}), \operatorname{prob}\left(f, k\right) = \operatorname{ite}\left(0 \le k, \frac{\operatorname{Polynomial}.\operatorname{coeff}\left(f, \operatorname{Int}.\operatorname{toNat}\left(k\right)\right)}{\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right)}, 0\right)$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.prob` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Section 4, page 9, defines p(n,k) = a(n,k)/∑ⱼ₌₀ⁿ a(n,j). For a nonnegative integer k, the mass is coefficient k.toNat divided by f(1); for negative k it is zero. Polynomial evaluation at one sums the coefficients.

**Definition 1.10 (StatLean.HypothesisTesting.stdNormalCDF).**

$$\forall (t: \mathbb{R}), \operatorname{StatLean}.\operatorname{HypothesisTesting}.\operatorname{stdNormalCDF}\left(t\right) = \operatorname{StatLean}.\operatorname{HypothesisTesting}.\operatorname{normalCDF}\left(0, 1, t\right)$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalCDF` (`✓ std3`).

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

StatLean.HypothesisTesting.normalCDF(m,v,t) is (gaussianReal m v (Set.Iic t)).toReal. Its specialization at m=0 and v=1 is the source expression (1/√(2π))∫₋∞ᵗ exp(−x²/2) dx.

**Definition 1.11 (StatLean.HypothesisTesting.stdNormalPDF).**

$$\forall (t: \mathbb{R}), \operatorname{StatLean}.\operatorname{HypothesisTesting}.\operatorname{stdNormalPDF}\left(t\right) = \frac{\operatorname{exp}\left(-\frac{(t)^{2}}{2}\right)}{\operatorname{Real}.\operatorname{sqrt}\left(2 \cdot \pi\right)}$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF` (`✓ std3`).

*Citation.* Junwei Lu and StatLean contributors (2026). *StatLean Fourier smoothing and Gaussian Hermite suppliers*. URL: <https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254>.

*Commentary.*

The density exp(−t²/2)/√(2π) equals the source expression (1/√(2π)) exp(−t²/2).

**Definition 1.12 (CLT).**

$$\forall (f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{R}\right)), (\operatorname{CLT}\left(f\right)) \Leftrightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\sum_{k \in \operatorname{filter}\left((k: \mathbb{N} \mapsto (k: \mathbb{R}) \le \operatorname{mu}\left(f\left(n\right)\right) + t \cdot \operatorname{sigma}\left(f\left(n\right)\right)), \operatorname{range}\left(\operatorname{natDegree}\left(f\left(n\right)\right) + 1\right)\right)} (\operatorname{prob}\left(f\left(n\right), (k: \mathbb{Z})\right)) - \operatorname{StatLean}.\operatorname{HypothesisTesting}.\operatorname{stdNormalCDF}\left(t\right)\right| < e), atTop\right)))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.CLT` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Section 4, page 8: “The coefficient a(n, k) is said to be asymptotically normal with mean μₙ and variance σₙ² by a central limit theorem if” limₙ→∞ supₜ∈ℝ |∑ₖ≤μₙ+tσₙ p(n,k) − (1/√(2π))∫₋∞ᵗ exp(−x²/2) dx| = 0. The central limit convention uses an epsilon bound uniform in the real threshold t. The range includes all natural indices through the polynomial degree. The normal CDF is StatLean.HypothesisTesting.stdNormalCDF.

**Definition 1.13 (LLT).**

$$\forall (f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{R}\right)), (\operatorname{LLT}\left(f\right)) \Leftrightarrow (\forall (e: \mathbb{R}), (0 < e) \Rightarrow (\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \forall (t: \mathbb{R}), \left|\operatorname{sigma}\left(f\left(n\right)\right) \cdot \operatorname{prob}\left(f\left(n\right), \left\lfloor \operatorname{mu}\left(f\left(n\right)\right) + t \cdot \operatorname{sigma}\left(f\left(n\right)\right)\right\rfloor\right) - \operatorname{StatLean}.\operatorname{HypothesisTesting}.\operatorname{stdNormalPDF}\left(t\right)\right| < e), atTop\right)))$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.LLT` (`✓ std3`).

*Citation.* Rong Zhang, James Jing Yu Zhao (2024). *Analytic properties of Speyer’s g-polynomial of uniform matroids*. DOI: [10.1007/s10114-026-4502-5](https://doi.org/10.1007/s10114-026-4502-5). URL: <https://arxiv.org/abs/2408.15506v1>.

*Commentary.*

Section 4, page 9: “The coefficient a(n, k) is said to be asymptotically normal with mean μₙ and variance σₙ² by a local limit theorem on the real set ℝ if” limₙ→∞ supₜ∈ℝ |σₙ p(n,⌊μₙ+tσₙ⌋) − (1/√(2π)) exp(−t²/2)| = 0. The local limit convention uses an epsilon bound uniform in t, with the literal integer floor of mu(f(n))+t*sigma(f(n)). The density is StatLean.HypothesisTesting.stdNormalPDF.

**Definition 1.14 (bernoulliPGF).**

$$\forall (p: \mathbb{R}), \operatorname{bernoulliPGF}\left(p\right) = \operatorname{C}\left(1 - p\right) + \operatorname{C}\left(p\right) \cdot X$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulliPGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial of a Bernoulli variable is C(1-p)+C(p)*X.

**Definition 1.15 (normalized).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \operatorname{normalized}\left(f\right) = \operatorname{C}\left((\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right))^{-(1)}\right) \cdot f$$

*Formalization.* `D5/S3/Analytic/Probability/BernoulliTriangularLimits.normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Normalization multiplies f by the constant inverse of its value at one.

**Lemma 1.16 (sigmaSq_mul).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \forall (h: \operatorname{Polynomial}\left(\mathbb{R}\right)), ((\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right) \ne 0) \land (\operatorname{Polynomial}.\operatorname{eval}\left(1, h\right) \ne 0)) \Rightarrow (\operatorname{sigmaSq}\left(f \cdot h\right) = \operatorname{sigmaSq}\left(f\right) + \operatorname{sigmaSq}\left(h\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Variance adds under polynomial multiplication when both values at one are nonzero.

**Lemma 1.17 (sigmaSq_C).**

$$\forall (c: \mathbb{R}), \operatorname{sigmaSq}\left(\operatorname{C}\left(c\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant polynomial has zero sigmaSq.

**Lemma 1.18 (sigmaSq_X).**

$$\operatorname{sigmaSq}\left((X: \operatorname{Polynomial}\left(\mathbb{R}\right))\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The deterministic shift X has zero variance.

**Theorem 1.19 (factorization_moments).**

$$\forall (f: \operatorname{Polynomial}\left(\mathbb{R}\right)), \forall (m: \mathbb{N}), \forall (p: \operatorname{Fin}\left(m\right) \to \operatorname{unitInterval}), (\operatorname{normalized}\left(f\right) = X \cdot \prod_{i: \operatorname{Fin}\left(m\right)} (\operatorname{bernoulliPGF}\left((p\left(i\right): \mathbb{R})\right))) \Rightarrow ((\operatorname{Polynomial}.\operatorname{eval}\left(1, f\right) \ne 0) \land ((\operatorname{mu}\left(f\right) = 1 + \operatorname{rowMean}\left(p\right)) \land (\operatorname{sigmaSq}\left(f\right) = \operatorname{rowVariance}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.factorization_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shifted Bernoulli factorization fixes the total mass, mean and variance of the normalized coefficient law.

**Theorem 1.20 (bernoulli_polynomial_uniform_limits).**

$$\forall (f: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{R}\right)), \forall (m: \mathbb{N} \to \mathbb{N}), \forall (p: \forall (n: \mathbb{N}), \operatorname{Fin}\left(m\left(n\right)\right) \to \operatorname{unitInterval}), ((\operatorname{Filter}.\operatorname{Eventually}\left((n: \mathbb{N} \mapsto \operatorname{normalized}\left(f\left(n\right)\right) = X \cdot \prod_{i: \operatorname{Fin}\left(m\left(n\right)\right)} (\operatorname{bernoulliPGF}\left((p\left(n, i\right): \mathbb{R})\right))), atTop\right)) \land (\operatorname{Tendsto}\left((n: \mathbb{N} \mapsto \operatorname{rowVariance}\left(p\left(n\right)\right)), atTop, atTop\right))) \Rightarrow ((\operatorname{CLT}\left(f\right)) \land (\operatorname{LLT}\left(f\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_polynomial_uniform_limits` (`✓ std3`). ∎

*Citation.* Edward A. Bender (1973). *Central and local limit theorems applied to asymptotic enumeration*. DOI: [10.1016/0097-3165(73)90038-1](https://doi.org/10.1016/0097-3165(73)90038-1). URL: <https://doi.org/10.1016/0097-3165(73)90038-1>.

*Commentary.*

For polynomial arrays with an eventual shifted Bernoulli factorization, variance divergence yields both the uniform central and local limits.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.CLT`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.LLT`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulliPGF`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_array_uniform_lattice_limit`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.bernoulli_polynomial_uniform_limits`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.factorization_moments`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.mu`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.normalized`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.prob`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMass`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowMean`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.rowVariance`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigma`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_C`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_X`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.sigmaSq_mul`
- Truth anchor: `D5/S3/Analytic/Probability/BernoulliTriangularLimits.uniform_lattice_limit_to_floor`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalCDF`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF`
- Dependency: [D5/S3/Analytic/Probability/UniformCDFConvergence](UniformCDFConvergence.md)
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers](../../TotalVariation/Asymptotics/StatLeanFourierSuppliers.md)
