# Twelvefold Orbit Multiplicity

## Abstract

Twelvefold symmetry counts equal orbits by their stabilizer.

**Theorem 1.1 (Twelvefold orbit multiplicity).**

$$\forall G, X, Y, x, O,\ \operatorname{card}(G) = 12, Y \equiv \operatorname{Fin}(O) \times \operatorname{orbit}(G, x),\ \operatorname{card}(Y) \times \operatorname{card}(\operatorname{stabilizer}(G, x)) = 12 \times O \land \operatorname{card}(Y) = 12 \times O/\operatorname{card}(\operatorname{stabilizer}(G, x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/TwelveOrbitMultiplicity.twelve_orbit_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Y is the disjoint parameterization of O copies of one orbit under a finite group G of cardinality twelve, Mathlib's exact orbit-stabilizer identity gives card(Y) times the stabilizer size equals 12O. Nonemptiness of the stabilizer then gives exact natural-number division and the recorded multiplicity formula.

This closes only the multiplicity formula in appendix E.78. The four numerical examples, oriented narrow-class account, and glide interpretation in the same atom are not asserted.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/TwelveOrbitMultiplicity.twelve_orbit_multiplicity`
