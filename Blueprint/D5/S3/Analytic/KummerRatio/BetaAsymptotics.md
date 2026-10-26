# Beta integral endpoint asymptotics

## Abstract

Gamma limits for exponentially weighted beta integrals.

**Theorem 1.1 (Exponential concentration at the endpoint).**

Lean statement: `D5/S3/Analytic/KummerRatio/BetaAsymptotics.tendsto_beta_laplace`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/KummerRatio/BetaAsymptotics.tendsto_beta_laplace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real parameters s and d, multiply the integral from zero to one of exp(xt) times t to the power s-1 times (1-t) to the power d-1 by exp(-x) times x to the power d. The resulting quantity tends to Gamma(d) as x tends to positive infinity.

The normalized Gamma density gives an approximate identity on the real line. Reflecting the integration variable places the concentration point at zero. The remaining endpoint weight is integrable for every positive s and continuous at zero, including when its other endpoint is singular. The approximate identity theorem therefore supplies the limit without a boundedness assumption at that endpoint.

## References

- Truth anchor: `D5/S3/Analytic/KummerRatio/BetaAsymptotics.tendsto_beta_laplace`
