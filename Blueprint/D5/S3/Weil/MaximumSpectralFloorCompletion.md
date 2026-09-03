# Maximum Spectral-Floor Completion

## Abstract

Residual positivity and full-spectrum white-floor feasibility have the same maximum.

**Theorem 1.1 (Maximum spectral-floor completion).**

$$\forall Spectrum \in \operatorname{Type}\left(\right), Reading \in \operatorname{Type}\left(\right), check \in \operatorname{AddMonoidHom}\left(Spectrum, Reading\right), white \in \operatorname{NNReal}\left(\right) \to Spectrum, delta \in Reading, source \in Reading,\; \left(\forall floor \in \operatorname{NNReal}\left(\right),\; check\left(white\left(floor\right)\right) = \operatorname{toReal}\left(floor\right) \cdot delta\right) \Rightarrow \left(\left(\forall floor \in \operatorname{NNReal}\left(\right),\; \operatorname{ResidualFeasible}\left(check, delta, source, floor\right) \Leftrightarrow \operatorname{FullSpectrumFeasible}\left(check, white, source, floor\right)\right) \land \operatorname{sSup}\left(\{floor \mid \operatorname{ResidualFeasible}\left(check, delta, source, floor\right)\}\right) = \operatorname{sSup}\left(\{floor \mid \operatorname{FullSpectrumFeasible}\left(check, white, source, floor\right)\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/MaximumSpectralFloorCompletion.maximum_spectral_floor_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive spectrum carrier packages nonnegativity. A floor is locally feasible when removing its normalized white reading leaves the reading of a positive residual spectrum.

From a local residual, adding the white spectrum constructs an explicit full-spectrum witness. Conversely, a full-spectrum decomposition returns its residual as the local witness.

Thus the two feasible-floor predicates agree pointwise. Their defining sets are equal, so their conditionally complete suprema are equal, including the empty or unbounded cases supplied by NNReal.

## References

- Truth anchor: `D5/S3/Weil/MaximumSpectralFloorCompletion.maximum_spectral_floor_completion`
