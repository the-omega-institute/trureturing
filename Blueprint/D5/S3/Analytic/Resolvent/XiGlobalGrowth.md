# Global Growth of the Riemann Xi Function

## Abstract

The classical pole-removed xi function satisfies a uniform exponential bound on the complex plane.

**Theorem 1.1 (A uniform log-linear growth bound).**

$$\exists C\in\mathbb{R},C>0\land\forall s\in\mathbb{C},\Vert\xi(s)\Vert\le\exp(C(1+\Vert s\Vert)(1+\log(1+\Vert s\Vert)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Resolvent/XiGlobalGrowth.xi_reading_norm_le_exp_log_linear` (`✓ std3`). ∎

*Citation.* Jeffrey C. Lagarias (2007). *Li Coefficients for Automorphic L-Functions*. DOI: [10.5802/aif.2311](https://doi.org/10.5802/aif.2311).

*Commentary.*

There is one positive real constant C such that the displayed bound holds for every complex s. Here xi is the classical Riemann xi function, with xi(0) = xi(1) = 1/2. Its exponent is C times (1 + norm(s)) times (1 + log(1 + norm(s))).

Lagarias's order-one theorem is compatible with this estimate. The proof uses the symmetric theta-tail Mellin integral for the pole-removed completion. Continuity controls the compact initial interval, while exponential theta decay controls the remaining half-line. A logarithmic estimate bounds both complex powers uniformly in s by an integrable exponential majorant. Integration and the polynomial xi factor then give the asserted constant.

The estimate is unconditional and includes both endpoints. Since 1 + log(r) is at most 3 times r^(1/2) for r at least one, it also gives the exp(C r^(3/2)) bound used by the normalized resolvent. No identity between Li coefficients and an infinite zero sum is asserted.

## References

- Truth anchor: `D5/S3/Analytic/Resolvent/XiGlobalGrowth.xi_reading_norm_le_exp_log_linear`
- Dependency: [D5/S3/Analytic/CompletedZetaMellinReconstruction](../CompletedZetaMellinReconstruction.md)
