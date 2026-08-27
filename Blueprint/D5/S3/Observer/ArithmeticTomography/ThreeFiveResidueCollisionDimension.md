# Three-Five Residue Collision and Dimension

## Abstract

The three-five coordinate pair has its explicit collision, while the full system has statistical dimension three.

**Theorem 1.1 (The three-five collision accompanies dimension three).**

$$\operatorname{Merges}\left(\{q3, q5\}, 0, 15\right) \land statisticalDimension = 3$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ArithmeticTomography/ThreeFiveResidueCollisionDimension.three_five_residue_collision_and_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical readings modulo three and modulo five identify zero with fifteen. This is the explicit collision required for the three-five coordinate pair.

On the same ZMod 30 state carrier, all three prime coordinates are complete and every two-coordinate selection is incomplete. Therefore the least complete coordinate count is three.

## References

- Truth anchor: `D5/S3/Observer/ArithmeticTomography/ThreeFiveResidueCollisionDimension.three_five_residue_collision_and_dimension`
- Dependency: [D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension](ResidueCoordinateDimension.md)
