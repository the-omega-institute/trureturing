# Zero Escape-Probability Characterization

## Abstract

Zero escape probability occurs exactly for identity twists in the two finite degeneracies.

**Theorem 1.1 (Identity twists characterize zero escape probability).**

$$\forall Y, [\operatorname{Fintype} Y] [\operatorname{Nonempty} Y], \forall f: Y \to Y, \forall A: \mathbb{N}, \operatorname{escapeProbability}\left(\operatorname{Fin}\left(A\right), f\right) = 0 \iff 0 < A \land f = \operatorname{id} \land (A = 1 \lor \operatorname{card}\left(Y\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/ZeroCharacterization.escape_probability_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite nonempty output alphabet Y, an endomorphism f, and A addresses, the frozen escape probability is zero exactly when A is positive, f is the identity, and either A=1 or Y is a singleton.

The frozen closed form reduces vanishing to equality between the fixed-point count and card(Y)^A. The fixed-point subtype bound then forces every output to be fixed. Injectivity of natural powers for card(Y) at least two leaves exponent one; the only alternative is the singleton alphabet.

This complements the probability-one endpoint without restating any frozen theorem. Both degeneracies are necessary: one address works for every identity twist, while a singleton alphabet works for every positive address count.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/ZeroCharacterization.escape_probability_eq_zero_iff`
- Dependency: [D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit](PoissonDomainLimit.md)
