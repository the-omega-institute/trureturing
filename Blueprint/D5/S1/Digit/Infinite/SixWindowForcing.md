# Local separation and six-window forcing

## Abstract

Local separation and six-window forcing.

**Theorem 1.1 (Shared colors force alternating source blocks).**

Lean statement: `D5/S1/Digit/Infinite/SixWindowForcing.result`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SixWindowForcing.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two legal infinite Boolean sources are observed through the same finite sequence of closed expanded cells. One step deletes three bits. The signed contraction is -g, where g is the cube of the reciprocal golden ratio. The four interior separation types have ordered labels (3,0), (0,5), (5,2), and (2,25).

At or below the finite-delay critical radius, the type-one pair forces three windows (3,3,5) and (0,3,0). Four common colors at type two force a return to type one with the two roles interchanged. Iterating this return forces the six-window words (3,3,5,0,3,0) and (0,3,0,3,3,5) for every requested number of repetitions. The last propagation uses only the last observed color.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SixWindowForcing.result`
- Dependency: [D5/S1/Digit/Infinite/CriticalPrefixSeparation](CriticalPrefixSeparation.md)
