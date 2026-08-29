# Agency Residual Witness

## Abstract

A hidden strategy difference is a concrete witness of agency residual.

**Theorem 1.1 (A hidden strategy difference is residual).**

$$\forall current: H \to M, profile: H \to P, x, y: H,\\{}(\operatorname{current}\left(x\right) = \operatorname{current}\left(y\right) \land \operatorname{profile}\left(x\right) \neq \operatorname{profile}\left(y\right)) \Rightarrow \operatorname{AgencyResidual}\left(current, profile, x, y\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyResidualWitness.hidden_strategy_difference_is_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume two histories have the same current-memory value but different strategy-profile values.

These two displayed facts are exactly the defining components of an agency-residual witness for that pair.

**Theorem 1.2 (A residual pair is separated by the paired readout).**

$$\forall current: H \to M, profile: H \to P, x, y: H,\\{}\operatorname{AgencyResidual}\left(current, profile, x, y\right) \Rightarrow \operatorname{pair}\left(\operatorname{current}\left(x\right), \operatorname{profile}\left(x\right)\right) \neq \operatorname{pair}\left(\operatorname{current}\left(y\right), \operatorname{profile}\left(y\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencySelf/AgencyResidualWitness.residual_separated_by_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the displayed pair lies in the agency residual.

Equality of the paired memory-profile values would imply equality of their profile components, contradicting the residual witness.

## References

- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyResidualWitness.hidden_strategy_difference_is_residual`
- Truth anchor: `D5/S3/Observer/AgencySelf/AgencyResidualWitness.residual_separated_by_pair`
