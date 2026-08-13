# Rounding the Second and Third Golden Powers

## Abstract

The second and third golden powers have exact adjacent integer rounding pairs.

**Theorem 1.1 (Golden-power floor and ceiling pairs).**

$$\lfloor\varphi^{3}\rfloor = 4 \land \operatorname{ceil}(\varphi^{3}) = 5 \land \lfloor\varphi^{2}\rfloor = 2 \land \operatorname{ceil}(\varphi^{2}) = 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/GoldenPowerRounding.golden_power_floor_ceil_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib supplies the golden-ratio quadratic identity, its strict bounds between one and two, and the exact floor and ceiling characterizations. These facts give the four adjacent integer rounding values directly.

This partial closure covers only the explicit rounding clause. The fiber-support interval, its distribution word, and the frequency claims remain outside this declaration.

## References

- Truth anchor: `D5/S1/Depth/GoldenPowerRounding.golden_power_floor_ceil_pairs`
