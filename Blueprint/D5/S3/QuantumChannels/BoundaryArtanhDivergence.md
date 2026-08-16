# Boundary Artanh Divergence

## Abstract

The mixed-state logarithmic tax diverges at the pure-state boundary.

**Theorem 1.1 (The logarithmic tax diverges at the boundary).**

$$\lim_{r\to1^{-}} \frac{r\cdot\operatorname{artanh}(r)}{2} = \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/BoundaryArtanhDivergence.logarithmic_tax_diverges_at_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As the mixed-state radius r approaches one from below, the coefficient r artanh(r) / 2 diverges to positive infinity. The proof first uses artanh(tanh b) = b and strict monotonicity of artanh to establish the boundary divergence of artanh itself. It then combines that divergence with the limiting positive factor r / 2.

This closes only the boundary clause c(r) = r artanh(r) / 2 with its logarithmic divergence in source atom appendix/E.173. It does not claim the atom's multiparameter budget, pure-state balancing, or metric-family classification statements.

## References

- Truth anchor: `D5/S3/QuantumChannels/BoundaryArtanhDivergence.logarithmic_tax_diverges_at_boundary`
