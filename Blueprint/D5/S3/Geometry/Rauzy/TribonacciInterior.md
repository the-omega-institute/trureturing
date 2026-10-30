# Interior of the Tribonacci Rauzy fractal

## Abstract

The exact exponent-zero Tribonacci Rauzy closure has nonempty interior at both secondary roots.

**Definition 1.1 (The concrete geometric input).**

Lean statement: `D5/S3/Geometry/Rauzy/TribonacciInterior.tribonacciCylinderSystem`

*Formalization.* `D5/S3/Geometry/Rauzy/TribonacciInterior.tribonacciCylinderSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two characteristic-root hypotheses supply every field of the separated-cylinder system for the existing Rauzy closure. The interior theorem consumes this same object.

**Theorem 1.2 (Nonempty interior at either non-Perron root).**

Lean statement: `D5/S3/Geometry/Rauzy/TribonacciInterior.rauzyFractal_interior_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Rauzy/TribonacciInterior.rauzyFractal_interior_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The only hypotheses are that z belongs to the existing complex Tribonacci characteristic-root multiset and is distinct from the real Tribonacci constant beta. K is exactly the existing closure of all finite Boolean digit sums starting at exponent zero and avoiding three consecutive ones. Neither a tile assumption nor positive area is supplied as a premise.

The three-step count recurrence with initial values 1, 2, 4 gives at least beta^Q names at every length Q. Resultant separation gives disjoint balls of radius sqrt(beta - 1) norm(z)^Q / 2 around these actual points of K. The identity beta norm(z)^2 = 1 bounds their total area below uniformly in Q. Continuity of the compact thickenings gives positive area for K.

Every finite word splits into an admissible prefix and suffix after terminal zero padding. The resulting affine images of compact K form a finite closed upper cover, which extends from the finite digit window to its closure. The synchronized cluster and persistent-hole construction then supplies a finite family of translates covering a disk and hence interior.

This is classical Rauzy geometry, not a novelty claim. Messaoudi's Propriétés arithmétiques et dynamiques du fractal de Rauzy, JTNB 10(1), 135–162, provides context; its exponent-three convention and imported tiling result are not premises of the formal proof. The theorem does not claim connectedness, tiling, or a numerical inner ball.

## References

- Truth anchor: `D5/S3/Geometry/Rauzy/TribonacciInterior.rauzyFractal_interior_nonempty`
- Truth anchor: `D5/S3/Geometry/Rauzy/TribonacciInterior.tribonacciCylinderSystem`
- Dependency: [D5/S0/Tower/Tribonacci/RauzyFractal](../../../S0/Tower/Tribonacci/RauzyFractal.md)
- Dependency: [D5/S0/Tower/Tribonacci/Separation](../../../S0/Tower/Tribonacci/Separation.md)
- Dependency: [D5/S3/Geometry/Rauzy/Interior](Interior.md)
