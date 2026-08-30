# Chebyshev Slack Positivity

## Abstract

A nonnegative real spectral coordinate compactifies into the closed unit interval, and its first-kind Chebyshev slack lies between zero and one.

**Theorem 1.1 (Chebyshev slack bounds).**

$$\forall N \in \operatorname{Nat}\left(\right), a \in \operatorname{Real}\left(\right), x \in \operatorname{Real}\left(\right),\; \left(\frac{1}{4} < a \land 0 \le x\right) \Rightarrow \operatorname{let} compactCoordinate = \frac{x - a}{x + a}, \operatorname{let} slack = 1 - \operatorname{eval}\left(\operatorname{ChebyshevT}\left(\operatorname{Real}\left(\right), N\right), compactCoordinate\right)^{2}, compactCoordinate \in \operatorname{Icc}\left(-1, 1\right) \land slack \in \operatorname{Icc}\left(0, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity.chebyshev_slack_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source rational coordinate is constructed directly from the nonnegative input and the scale above one quarter.

Its denominator is positive, so ordered-field division gives the coordinate bounds. The standard Chebyshev interval estimate then yields the two-sided slack bound.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/ChebyshevSlackPositivity.chebyshev_slack_bounds`
