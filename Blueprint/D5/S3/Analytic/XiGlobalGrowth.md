# Global Growth of the Riemann Xi Function

## Abstract

The classical pole-removed xi function satisfies a uniform exponential bound on the complex plane.

**Theorem 1.1 (A uniform three-halves growth bound).**

$$\exists C\in\mathbb{R},C>0\land\forall s\in\mathbb{C},\Vert\xi(s)\Vert\le\exp(C(1+\Vert s\Vert)^{\frac{3}{2}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/XiGlobalGrowth.xi_reading_norm_le_exp_three_halves` (`✓ std3`). ∎

*Citation.* Jeffrey C. Lagarias (2007). *Li Coefficients for Automorphic L-Functions*. DOI: [10.5802/aif.2311](https://doi.org/10.5802/aif.2311).

*Commentary.*

There is one positive real constant C such that the displayed bound holds for every complex s. Here xi is the classical Riemann xi function, with xi(0) = xi(1) = 1/2, and the exponent is the real number three halves.

Lagarias's order-one theorem implies this weaker estimate. The proof here uses the symmetric theta-tail Mellin integral for the pole-removed completion. Continuity controls the compact initial interval, while exponential theta decay controls the remaining half-line. A logarithmic estimate bounds both complex powers uniformly in s by an integrable exponential majorant. Integration and the polynomial xi factor then give the asserted constant.

The estimate is unconditional and includes both endpoints. It supplies a norm bound for subsequent complex-analytic estimates; no identity between Li coefficients and an infinite zero sum is asserted.

## References

- Truth anchor: `D5/S3/Analytic/XiGlobalGrowth.xi_reading_norm_le_exp_three_halves`
- Dependency: [D5/S3/Analytic/CompletedZetaMellinReconstruction](CompletedZetaMellinReconstruction.md)
