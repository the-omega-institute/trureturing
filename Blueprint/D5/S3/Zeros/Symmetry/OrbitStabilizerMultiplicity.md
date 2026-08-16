# Orbit-Stabilizer Multiplicity

## Abstract

Orbit size in a four-element group action is four divided by stabilizer size.

**Theorem 1.1 (Four-group orbit size is four divided by stabilizer size).**

$$\forall G, X, x,\ \operatorname{card}(G) = 4 \Rightarrow \operatorname{card}(\operatorname{orbit}(G, x)) = 4/\operatorname{card}(\operatorname{stabilizer}(G, x)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/OrbitStabilizerMultiplicity.orbit_card_eq_four_div_stabilizer_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite group G of cardinality four acting on X, the standard orbit-stabilizer theorem gives card(orbit G x) times card(stabilizer G x) = card(G). The pinned Mathlib theorem MulAction.card_orbit_mul_card_stabilizer_eq_card_group supplies that identity, and nonemptiness of the stabilizer permits exact natural-number division.

This closes only the orbit-stabilizer multiplicity clause of appendix E.120. The reported zero counts, symmetry census, and methodological postmortem in the same atom are not asserted.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/OrbitStabilizerMultiplicity.orbit_card_eq_four_div_stabilizer_card`
