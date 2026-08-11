# Golden Fiber Coordinates

## Abstract

Golden fiber coordinates are explicit differences of two Beatty readings.

**Theorem 1.1 (Fiber coordinates are golden Beatty readings).**

$$\operatorname{fiberA}\left(v\right) = \left\lfloor\frac{v + 1}{\varphi}\right\rfloor - \left\lfloor\frac{v + 1}{\varphi^{2}}\right\rfloor \land \left(\operatorname{fiberB}\left(v\right) = \left\lfloor\frac{v + 1}{\varphi^{2}}\right\rfloor \land \operatorname{fiberA}\left(v\right) + \operatorname{fiberB}\left(v\right) = \left\lfloor\frac{v + 1}{\varphi}\right\rfloor\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GoldenFiberCoordinates.golden_fiber_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive index v, begin with the shifted reading S(v) = floor((v+1) phi) - 1 and define the integral coordinates a(v) = 2 S(v) - 3v and b(v) = 2v - S(v). The second coordinate is floor((v+1)/phi^2), the first is the difference between the floor readings at 1/phi and 1/phi^2, and their sum is the reading at 1/phi. These are one coupled coordinate identity: the first and sum equations follow algebraically once the second is known.

Pinned Mathlib was searched before proving. It supplies the exact golden-ratio square, inverse, and irrationality declarations, its generic Beatty-sequence development, and the integer floor and ceiling laws. It contains no declaration for these fiber-coordinate formulas. The proof is therefore new assembly: it rewrites 1/phi as phi-1 and 1/phi^2 as 2-phi, then uses irrationality to turn the ceiling of a positive integer multiple of phi into its floor plus one.

## References

- Truth anchor: `D5/S1/Words/GoldenFiberCoordinates.golden_fiber_coordinates`
