# Integer grid counts in shifted balls

## Abstract

The normalized integer grid count in a closed three-dimensional ball tends to its unit volume for every fixed center.

**Theorem 1.1 (The normalized count at a fixed center).**

$$\lim_{r \to \infty} \frac{C\left(c, r\right)}{r^{3}} = \frac{4\pi}{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Counting/ShiftedBallCount.shifted_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed center c in Euclidean three-space, C(c,r) counts the points of the integer coordinate grid in the closed ball of radius r with center c.

The standard coordinate map preserves volume. The centered unit ball is bounded and measurable, its frontier is a sphere of volume zero, and its volume is 4π/3. Dilations are nested for positive radii. These facts give the centered limit by Mathlib's tendsto_card_div_pow_atTop_volume'.

Write d for the distance from c to the origin. The centered balls of radii r−d and r+d enclose the shifted count from below and above. For either fixed shift the cubed ratio of the shifted radius to r tends to one, so the two normalized bounds have the same limit.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Counting/ShiftedBallCount.shifted_limit`
