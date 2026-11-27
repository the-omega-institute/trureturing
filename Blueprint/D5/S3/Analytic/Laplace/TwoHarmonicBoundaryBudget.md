# Two-harmonic boundary budget

## Abstract

Three boundary values of a positive Laplace transform give a lower bound at zero frequency.

**Theorem 1.1 (Lower bound from the first two harmonics).**

$$\begin{aligned}\forall \sigma > 0,\quad(y \mapsto \exp(-\sigma \cdot y)) \in \left(L^{1}\right)\left(\mu\right)\\\lim_{\sigma\to0^{+}} A\left(\sigma, 0\right) = z_{0},\quad\lim_{\sigma\to0^{+}} A\left(\sigma, \gamma\right) = z_{1},\quad\lim_{\sigma\to0^{+}} A\left(\sigma, 2 \cdot \gamma\right) = z_{2}\\\longrightarrow \frac{\sqrt{\left\lVert z_{2} \right\rVert^{2} + 8 \cdot \left\lVert z_{1} \right\rVert^{2}} - \left\lVert z_{2} \right\rVert}{2} \le \Re(z_{0})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/TwoHarmonicBoundaryBudget.two_harmonic_boundary_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let μ be a positive measure on the real line and let γ be real. For every σ > 0 assume that y ↦ exp(−σy) is μ-integrable. Define A(σ,t) as σ times the integral of exp(−(σ+it)y) against μ. Assume the three right-hand limits in the display, with complex values z₀, z₁ and z₂.

Conjugacy supplies the negative frequencies. Apply boundary Gram positivity at 0, γ and 2γ with coefficients u, vw and uw², where w has unit norm. When a = ‖z₁‖ is positive, choose w so that wz₁ = −a. Writing b = ‖z₂‖ and λ for the displayed lower bound, the choice u = λ and v = 2a gives the estimate by λ² + bλ = 2a². For a = 0, the middle coefficient alone gives the bound. For z₂ = 0, the lower bound simplifies to √2 ‖z₁‖.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/TwoHarmonicBoundaryBudget.two_harmonic_boundary_budget`
- Dependency: [D5/S3/Analytic/Laplace/PositiveSpectralBudget](PositiveSpectralBudget.md)
