# Exponential Growth Bound for Metallic Coefficients

## Abstract

The coefficients of every integral q-metallic solution admit a uniform exponential bound in their degree.

**Theorem 1.1 (An exponential coefficient majorant).**

Lean statement: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth.coefficient_growth`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth.coefficient_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Guo-Niu Han, Emmanuel Pedon (2025). *Hankel continued fractions and Hankel determinants for q-deformed metallic numbers*. DOI: [10.48550/arXiv.2502.05993](https://doi.org/10.48550/arXiv.2502.05993). URL: <https://arxiv.org/abs/2502.05993v2>.

*Commentary.*

For every positive integer n, every integral formal power series Phi with constant coefficient one satisfying q Phi^2 + ((1+q^n)(1-q)-q[n]_q)Phi = 1, and every nonnegative integer m, the absolute value of [q^m]Phi is at most (4(n+5))^m. Here [n]_q = 1+q+...+q^{n-1}. The estimate includes m equal to zero and the golden case n equal to one.

## References

- Truth anchor: `D5/S3/Combinatorics/MetallicHankel/MetallicHankelUnboundedGrowth.coefficient_growth`
- Dependency: [D5/S3/Combinatorics/MetallicHankel/MetallicHankelDefs](MetallicHankelDefs.md)
