# Symmetric homogeneous beta lifting

## Abstract

Beta lifting preserves symmetric balancing for arbitrary real coefficients.

The degree N and coefficient function c are arbitrary. No coefficient sign assumption is imposed. The homogeneous polynomial is evaluated on a line of fixed coordinate sum, and its lift replaces the powers by rising factorials.

**Definition 1.1 (Homogeneous monomial expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{polynomial}\left(c, N, x, y\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{c}\left(k\right) \cdot x^{k} \cdot y^{N - k})$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The polynomial is the finite sum of c(k)x^k y^(N-k), including both endpoints.

**Definition 1.2 (Rising factorial lift).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{lift}\left(c, N, u, v\right) = \sum_{k \in \operatorname{Finset.range}\left(N + 1\right)} (\operatorname{c}\left(k\right) \cdot \operatorname{Polynomial.eval}\left(u, \operatorname{ascPochhammer}\left(\mathbb{R}, k\right)\right) \cdot \operatorname{Polynomial.eval}\left(v, \operatorname{ascPochhammer}\left(\mathbb{R}, N - k\right)\right))$$

*Formalization.* `D5/S3/Analytic/KarpZhangNinh/Beta.lift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same coefficient array multiplies the two complementary rising factorials.

**Theorem 1.3 (Continuity of the homogeneous slice).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \operatorname{Continuous}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every homogeneous slice is continuous because it is a finite sum of products of integer powers.

**Theorem 1.4 (Continuity of the lifted slice).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (S: \mathbb{R}), \operatorname{Continuous}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{lift}\left(c, N, s, S - s\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lifted slice is a polynomial in its real parameter, so it is continuous on the full real line.

**Theorem 1.5 (Symmetry of the homogeneous expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow (\forall (x: \mathbb{R}), \forall (y: \mathbb{R}), \operatorname{polynomial}\left(c, N, x, y\right) = \operatorname{polynomial}\left(c, N, y, x\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reflection of the finite index k to N-k proves coordinate symmetry when the coefficients are symmetric.

**Theorem 1.6 (Symmetry of the rising factorial expansion).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow (\forall (u: \mathbb{R}), \forall (v: \mathbb{R}), \operatorname{lift}\left(c, N, u, v\right) = \operatorname{lift}\left(c, N, v, u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same reflected finite sum proves symmetry of the lifted polynomial.

**Theorem 1.7 (Normalized beta moment identity).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), \forall (m: \mathbb{R}), \forall (d: \mathbb{R}), (0 < m + d) \Rightarrow ((0 < m - d) \Rightarrow (\operatorname{lift}\left(c, N, m + d, m - d\right) = \operatorname{Polynomial.eval}\left(2 \cdot m, \operatorname{ascPochhammer}\left(\mathbb{R}, N\right)\right) \cdot \operatorname{betaMean}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right)), m, d\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_eq_betaMean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrating each monomial against the beta density gives its Gamma quotient. KummerRatio.BetaIntegral.gamma_pochhammer converts the shifted Gamma factors to rising factorials. The remaining normalizer depends only on the total shape parameter.

**Theorem 1.8 (Weak comparison for arbitrary monotone integrands).**

$$\forall (W: \mathbb{R} \to \mathbb{R}), (\operatorname{ContinuousOn}\left(W, \operatorname{Set.Icc}\left(0, 1\right)\right)) \Rightarrow ((\forall (t: \mathbb{R}), (t \in \operatorname{Set.Icc}\left(0, 1\right)) \Rightarrow (\operatorname{W}\left(1 - t\right) = \operatorname{W}\left(t\right))) \Rightarrow ((\operatorname{MonotoneOn}\left(W, \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right)) \Rightarrow (\forall (m: \mathbb{R}), (0 < m) \Rightarrow (\operatorname{AntitoneOn}\left((\lambda (d: \mathbb{R}) \mapsto \operatorname{betaMean}\left(W, m, d\right)), \operatorname{Set.Ico}\left(0, m\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.betaMean_antiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adding a positive multiple of t(1-t) makes the integrand strictly increasing toward the midpoint while preserving its symmetry. IncompleteBeta.Comparison.betaMean_strictAntiOn compares the perturbed means. Linearity of the integral and the limit as the perturbation decreases to zero yield the weak comparison.

**Theorem 1.9 (Beta lifting preserves balancing).**

$$\forall (c: \mathbb{N} \to \mathbb{R}), \forall (N: \mathbb{N}), (\forall (k: \mathbb{N}), (k \le N) \Rightarrow (\operatorname{c}\left(N - k\right) = \operatorname{c}\left(k\right))) \Rightarrow ((\operatorname{MonotoneOn}\left((\lambda (t: \mathbb{R}) \mapsto \operatorname{polynomial}\left(c, N, t, 1 - t\right)), \operatorname{Set.Ioc}\left(0, \frac{1}{2}\right)\right)) \Rightarrow (\forall (S: \mathbb{R}), (0 \le S) \Rightarrow (\operatorname{MonotoneOn}\left((\lambda (s: \mathbb{R}) \mapsto \operatorname{lift}\left(c, N, s, S - s\right)), \operatorname{Set.Icc}\left(0, \frac{S}{2}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KarpZhangNinh/Beta.lift_monotoneOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive shapes, the beta moment identity and comparison of symmetric beta means show that the lift is nondecreasing as the coordinates approach equality. Continuity extends the inequality to shape zero. A zero total has only the point zero. This preservation theorem has no positivity hypothesis on c.

## References

- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.betaMean_antiOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_eq_betaMean`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_monotoneOn`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.lift_symm`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_continuous`
- Truth anchor: `D5/S3/Analytic/KarpZhangNinh/Beta.polynomial_symm`
- Dependency: [D5/S3/Analytic/IncompleteBeta/Comparison](../IncompleteBeta/Comparison.md)
- Dependency: [D5/S3/Analytic/KummerRatio/BetaIntegral](../KummerRatio/BetaIntegral.md)
