# Principal Strata Under Monotonicity

## Abstract

An almost-sure monotone Boolean response law has three possible principal strata, with masses fixed by the two potential-outcome marginals.

**Theorem 1.1 (A monotone Boolean response has three principal strata).**

$$\forall mass \in \operatorname{Prod}\left(Bool, Bool\right) \to Real,\; \left(\left(\forall pair \in \operatorname{Prod}\left(Bool, Bool\right),\; 0 \le mass\left(pair\right)\right) \land \left(mass\left(\operatorname{pair}\left(false, false\right)\right) + mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right) = 1 \land \left(\forall pair \in \operatorname{Prod}\left(Bool, Bool\right),\; \left(0 < mass\left(pair\right) \land \operatorname{fst}\left(pair\right) = true\right) \Rightarrow \operatorname{snd}\left(pair\right) = true\right)\right)\right) \Rightarrow \left(mass\left(\operatorname{pair}\left(true, false\right)\right) = 0 \land \left(mass\left(\operatorname{pair}\left(false, false\right)\right) = 1 - \left(mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right)\right) \land \left(mass\left(\operatorname{pair}\left(false, true\right)\right) = mass\left(\operatorname{pair}\left(false, true\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right) - \left(mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right)\right) \land mass\left(\operatorname{pair}\left(true, true\right)\right) = mass\left(\operatorname{pair}\left(true, false\right)\right) + mass\left(\operatorname{pair}\left(true, true\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/PrincipalStrata.principal_strata` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mass be a normalized nonnegative joint law on the Boolean pair of potential outcomes. Almost-sure monotonicity requires every positive-mass pair with first coordinate true to have second coordinate true.

The harmful pair therefore has zero mass. Expanding normalization then identifies the never, benefit, and always masses as one minus the treatment-one marginal, the difference of the two marginals, and the treatment-zero marginal, respectively.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/PrincipalStrata.principal_strata`
