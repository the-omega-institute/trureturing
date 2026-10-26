# The integral Golay construction and its exact minimum

## Abstract

The integral Golay construction and its exact minimum

**Theorem 1.1 (The exact quotient representation).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.representation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/IntegerLeech.representation` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The original admissibility conditions are equivalent to coordinates m plus twice an integer vector, with the same canonical parity bit, code residue and coordinate-sum congruence. The same integer representative determines both the real image and the raw coordinates in direct selfduality.

**Definition 1.2 (Literal integral congruence coordinates).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.Admissible`

*Formalization.* `D5/S3/Arith/Lattices/Golay/IntegerLeech.Admissible` (`✓ std3`).

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

An integer vector has a common parity bit m in zero or one; its quotient residue is a codeword, and its coordinate sum is congruent to four m modulo eight.

**Definition 1.3 (Additive closure is derived).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.integerLattice`

*Formalization.* `D5/S3/Arith/Lattices/Golay/IntegerLeech.integerLattice` (`✓ std3`).

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

For an arbitrary binary linear code containing the all-ones word, the literal congruence set is an additive subgroup. The odd plus odd carry is absorbed by the proved all-ones membership.

**Theorem 1.4 (Even scaled norms).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.squareSum_div_sixteen`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/IntegerLeech.squareSum_div_sixteen` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

For every doubly-even binary linear code and every actual admissible integer vector, the sum of coordinate squares is divisible by sixteen. Dividing by eight therefore gives an even integral squared norm.

**Theorem 1.5 (Every nonzero admissible integer vector has squared integer norm at least 32).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.construction_lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/IntegerLeech.construction_lower_bound` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

The even nonzero-residue case uses the minimum weight. The zero-residue case uses the coordinate-sum congruence to exclude a sole coordinate of size four. In the odd case every coordinate has absolute value at least one and divisibility by sixteen raises the bound from 24 to 32.

**Theorem 1.6 (The scaled pairing is integral).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.pairing_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/IntegerLeech.pairing_integral` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

Polarization, the derived additive closure and divisibility of all three squared norms by sixteen imply divisibility of the coordinate dot product by eight.

**Theorem 1.7 (Exact minimum four from actual encoded Golay words).**

Lean statement: `D5/S3/Arith/Lattices/Golay/IntegerLeech.minimum_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/IntegerLeech.minimum_norm` (`✓ std3`). ∎

*Citation.* John Leech (1967). *Notes on Sphere Packings*. DOI: [10.4153/CJM-1967-017-0](https://doi.org/10.4153/CJM-1967-017-0). URL: <https://doi.org/10.4153/CJM-1967-017-0>.

*Commentary.*

This theorem consumes the constructed Golay linear image and its proved double evenness and minimum weight. Twice the zero-one lift of its encoded octad is an admissible nonzero vector with square sum 32. Every nonzero admissible vector has square sum at least 32, so dividing by eight gives exact squared minimum four. Coordinate division by the real square root of eight gives the same real squared norm as the rational square sum divided by eight. Rank, unimodularity, uniqueness and all VOA, CFT or Monster realization claims remain outside this result.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.Admissible`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.construction_lower_bound`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.integerLattice`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.minimum_norm`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.pairing_integral`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.representation`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/IntegerLeech.squareSum_div_sixteen`
- Dependency: [D5/S3/Arith/Lattices/Golay/GolayEncoder](GolayEncoder.md)
