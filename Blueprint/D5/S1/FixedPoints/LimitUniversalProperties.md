# Universal Properties of Limits and Colimits

## Abstract

Colimit cocones are initial and limit cones are terminal.

**Theorem 1.1 (Colimits are initial and limits are terminal).**

$$(\operatorname{Nonempty}(\operatorname{IsColimit}(c)) \Leftrightarrow \operatorname{Nonempty}(\operatorname{IsInitial}(c))) \land (\operatorname{Nonempty}(\operatorname{IsLimit}(l)) \Leftrightarrow \operatorname{Nonempty}(\operatorname{IsTerminal}(l)))$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/LimitUniversalProperties.colimit_initial_and_limit_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any diagram F, a cocone c satisfies the colimit universal property exactly when it is an initial object in the category of cocones. Dually, a cone l satisfies the limit universal property exactly when it is terminal in the category of cones. Nonempty makes the existence of each universal-property structure propositional.

The pinned Mathlib source was searched before proving. Its equivalences Cocone.isColimitEquivIsInitial and Cone.isLimitEquivIsTerminal are exact matches, so the Lean proof only applies their forward and inverse maps.

The formal scope is Proposition 2 in source remark 27.559: the direct limit has the initial-cocone universal property and the inverse limit has the terminal-cone universal property. No claim is made here about state-space duality, Busch uniqueness, contextuality, Kolmogorov extension, or entropy and sharpness.

## References

- Truth anchor: `D5/S1/FixedPoints/LimitUniversalProperties.colimit_initial_and_limit_terminal`
