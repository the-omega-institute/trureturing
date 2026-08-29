# Golden Germ Zeta Meromorphic Half-Plane

## Abstract

The golden germ zeta is meromorphic above one over phi cubed and has no pole away from one over phi squared.

**Theorem 1.1 (Meromorphy and pole exclusion on the half-plane).**

$$\begin{aligned}germZeta: \mathbb{C} \to \mathbb{C},\\\forall s\in \mathbb{C}, \operatorname{germZeta}(s) := \operatorname{riemannZeta}(\varphi^{2} \times s) \times \prod_{p\in \operatorname{Primes}(\mathbb{N})}(1 - p^{-s \times \varphi^{2}}) \times \sum_{v\in \mathbb{N}}p^{-s \times \operatorname{o5Beta}(v)},\\\operatorname{MeromorphicOn}(germZeta, \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\}) \land\\(\forall s\in \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\}, s \neq \frac{1}{\varphi^{2}} \Rightarrow \operatorname{AnalyticAt}(\mathbb{C}, germZeta, s)) \land\\\forall s\in \{s\in \mathbb{C} \mid \frac{1}{\varphi^{3}} < \Re(s)\}, s \neq \frac{1}{\varphi^{2}} \Rightarrow 0 \leq \operatorname{meromorphicOrderAt}(germZeta, s).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Isolation/GoldenGermZetaMeromorphicHalfPlane.golden_germ_zeta_meromorphic_half_plane` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the germ zeta function be the Riemann zeta function at phi squared times s, multiplied by the normalized golden prime product. On the half-plane where the real part of s exceeds one over phi cubed, this function is meromorphic.

At one over phi squared, GoldenGermZetaSimplePole supplies meromorphy and the exact simple-pole order. At every other point of the half-plane, the Riemann zeta factor avoids its pole and GoldenGermNormalizedFactorRegularity makes the normalized product analytic.

Thus the germ is analytic at every point in the region except one over phi squared. The nonnegative meromorphic-order conjunct records pointwise that none of those analytic points is a pole.

STOPPING JUSTIFICATION: this theorem says nothing about the zero set, nothing at or to the left of the line where the real part of s equals one over phi cubed, and does not compute the order at one over phi squared; the upstream simple-pole node does so.

## References

- Truth anchor: `D5/S3/Analytic/Isolation/GoldenGermZetaMeromorphicHalfPlane.golden_germ_zeta_meromorphic_half_plane`
- Dependency: [D5/S3/Analytic/Isolation/GoldenGermZetaSimplePole](GoldenGermZetaSimplePole.md)
- Dependency: [D5/S3/Analytic/Regularity/GoldenGermNormalizedFactorRegularity](../Regularity/GoldenGermNormalizedFactorRegularity.md)
