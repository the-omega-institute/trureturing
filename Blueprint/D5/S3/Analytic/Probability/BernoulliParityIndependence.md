# Independence of two Bernoulli parity events

## Abstract

Independence of parity tests under a finite Bernoulli product law.

**Theorem 1.1 (Disjoint supports and fair bits).**

Lean statement: `D5/S3/Analytic/Probability/BernoulliParityIndependence.parity_events_independent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BernoulliParityIndependence.parity_events_independent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each bit has probability in the half-open interval from zero to one half, with zero excluded and one half included. For each of two subsets, fix the required parity of its bits. The joint event mass equals the product of the individual event masses exactly when the supports are disjoint or a fair bit belongs to their symmetric difference. Multiplying the parity characters cancels the shared signs. In the covariance, the remaining bias product over the symmetric difference multiplies one minus the squared bias product over the intersection. A fair bit can make the first factor vanish. The second factor vanishes exactly when the intersection is empty.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BernoulliParityIndependence.parity_events_independent_iff`
