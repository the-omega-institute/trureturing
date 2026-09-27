# Asymptotic density of sets of naturals

## Abstract

Upper and lower asymptotic densities of sets of naturals, and subadditivity of the upper density.

The counting function of a set of naturals is the number of its members below a bound. Dividing by the bound and passing to the limit superior and the limit inferior gives the upper and the lower density; the set has a density when the two agree. Schnirelmann density, which Mathlib carries, is a different quantity: it is an infimum over all bounds rather than a limit, and it is not used here.

**Definition 1.1 (Upper density).**

Lean statement: `D5/S3/Arith/Density/AsymptoticDensity.upperDensity`

*Formalization.* `D5/S3/Arith/Density/AsymptoticDensity.upperDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

upperDensity A is the limit superior along the natural numbers of the count of members of A below n, divided by n.

**Definition 1.2 (Lower density).**

Lean statement: `D5/S3/Arith/Density/AsymptoticDensity.lowerDensity`

*Formalization.* `D5/S3/Arith/Density/AsymptoticDensity.lowerDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

lowerDensity A is the limit inferior of the same ratio.

**Definition 1.3 (Having a density).**

Lean statement: `D5/S3/Arith/Density/AsymptoticDensity.HasDensity`

*Formalization.* `D5/S3/Arith/Density/AsymptoticDensity.HasDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HasDensity A d holds when the lower and upper densities of A agree and that common value is d.

**Theorem 1.4 (The upper density is subadditive).**

Lean statement: `D5/S3/Arith/Density/AsymptoticDensity.upperDensity_union_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/AsymptoticDensity.upperDensity_union_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The upper density of a union is at most the sum of the upper densities. The proof runs through the finite counting functions, where the union bound is exact, and then through the limit superior of a sum, which is bounded by the sum of the limits superior once both are finite.

## References

- Truth anchor: `D5/S3/Arith/Density/AsymptoticDensity.HasDensity`
- Truth anchor: `D5/S3/Arith/Density/AsymptoticDensity.lowerDensity`
- Truth anchor: `D5/S3/Arith/Density/AsymptoticDensity.upperDensity`
- Truth anchor: `D5/S3/Arith/Density/AsymptoticDensity.upperDensity_union_le`
