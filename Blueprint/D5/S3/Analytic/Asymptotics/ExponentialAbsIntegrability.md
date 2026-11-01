# Integrability of two-sided exponential decay

## Abstract

The two-sided real exponential is integrable at every positive rate.

**Theorem 1.1 (Exponential decay on the real line).**

$$\forall a \in Real,\; 0 < a \Rightarrow Integrable\left((x:Real \mapsto exp\left(-((a*\left|x\right|))\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability.integrable_exp_neg_mul_abs` (`✓ std3`). ∎

*Citation.* Bastiaan J Braams; The Tau Ceti contributors (2026). *Gamma bounds and Mellin-Barnes contour closure*. URL: <https://github.com/bjbraams/lean-DLMF/tree/560b9475f35bbc6e4f5296631298859825091f7f>.

*Commentary.*

For every positive real a the real function x maps to exp(-a*abs(x)) is integrable with respect to Lebesgue measure. Splitting the line at zero reduces this to the two exponential half-line integrals.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability.integrable_exp_neg_mul_abs`
