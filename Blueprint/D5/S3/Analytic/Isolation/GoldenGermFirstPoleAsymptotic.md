# Golden Germ First-Pole Asymptotic

## Abstract

The golden Euler germ has a positive right-hand first-pole asymptotic.

**Theorem 1.1 (The first golden pole has a positive quantitative asymptotic).**

$$\begin{aligned}P: \mathbb{R} \to \mathbb{C},\\\forall sigma\in \mathbb{R}, \operatorname{P}(sigma) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}\sum_{v\in \mathbb{N}}p^{-sigma \times \operatorname{o5Beta}(v)},\\G: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{G}(s) := \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\a := \frac{1}{\varphi^{2}},\\c := \operatorname{G}(\frac{1}{\varphi^{2}}) / \varphi^{2},\\\operatorname{Tendsto}((sigma: \mathbb{R}) \mapsto \Re((sigma - \frac{1}{\varphi^{2}}) \times \operatorname{P}(sigma)), \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \operatorname{Ioi}(\frac{1}{\varphi^{2}})), \operatorname{nhds}(\Re(\operatorname{G}(\frac{1}{\varphi^{2}}) / \varphi^{2}))) \land\\\operatorname{Tendsto}((sigma: \mathbb{R}) \mapsto \operatorname{Im}((sigma - \frac{1}{\varphi^{2}}) \times \operatorname{P}(sigma)), \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \operatorname{Ioi}(\frac{1}{\varphi^{2}})), \operatorname{nhds}(0)) \land\\\operatorname{Tendsto}((sigma: \mathbb{R}) \mapsto \Re(\operatorname{P}(sigma)), \operatorname{nhdsWithin}(\frac{1}{\varphi^{2}}, \operatorname{Ioi}(\frac{1}{\varphi^{2}})), atTop).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/GoldenGermFirstPoleAsymptotic.golden_germ_first_pole_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem is the next real-boundary node in the golden Euler germ extraction ladder of OACTC parts 580 and 581. It advances the remaining boundary from an explicit complex residue and real-axis positivity to a directional quantitative asymptotic.

Let a be one over phi squared, P the golden Euler prime product, and c equal G(a) over phi squared. Pulling the frozen punctured complex residue limit back along the real embedding and applying the frozen factorization gives real part convergence of (sigma-a)P(sigma) to the positive c. The frozen real-axis theorem makes the scaled imaginary part identically zero on the right-hand ray.

Since sigma-a approaches zero through positive values, its reciprocal tends to positive infinity. Multiplying that reciprocal by the scaled real part, whose limit c.re is strictly positive, proves that Re(P(sigma)) tends to positive infinity.

STOPPING JUSTIFICATION: this is only a local, right-hand real-axis statement at the first golden pole. It does not assert a Tauberian theorem, coefficient asymptotics, O-5, the Riemann hypothesis, a complex zero-free region, or behavior at any other boundary point.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/GoldenGermFirstPoleAsymptotic.golden_germ_first_pole_asymptotic`
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermRealAxisPositivity](../EulerGerm/GoldenGermRealAxisPositivity.md)
- Dependency: [D5/S3/Analytic/EulerGerm/GoldenGermZetaFactorization](../EulerGerm/GoldenGermZetaFactorization.md)
- Dependency: [D5/S3/Analytic/Isolation/GoldenGermZetaResidue](GoldenGermZetaResidue.md)
