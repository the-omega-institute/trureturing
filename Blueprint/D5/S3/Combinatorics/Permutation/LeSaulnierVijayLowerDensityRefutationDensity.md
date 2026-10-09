# Counting the Eleven-Adic Interval Construction

## Abstract

The eleven-adic interval construction has lower density at least four fifteenths.

**Definition 1.1 (Stage scale).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural stage index k, the scale M is the natural quotient of eleven to the power k plus one by two.

**Definition 1.2 (The two stage intervals).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Stage k is the union of the inclusive intervals from twice M to three M minus one, and from six M minus two to eleven M minus five.

**Definition 1.3 (The infinite witness set).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S`

*Formalization.* `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The witness consists of one and all integers in any of the stage intervals.

**Theorem 1.4 (The exact doubled scale).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.twice_M`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.twice_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, twice the scale is exactly eleven to the power k plus one; eleven to every natural power is odd.

**Theorem 1.5 (Every scale is positive).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale is strictly positive for every natural stage index.

**Theorem 1.6 (The scale recurrence).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The next scale is eleven times the present scale minus five.

**Theorem 1.7 (The scales strictly increase).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_strictMono`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale function is strictly increasing on the natural numbers.

**Theorem 1.8 (Stage bounds).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of stage k is at least twice its scale and at most the scale of stage k plus one.

**Theorem 1.9 (The witness uses positive integers).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every integer in the witness set is strictly positive.

**Theorem 1.10 (Lower density at least four fifteenths).**

Lean statement: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.lowerDensityBound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.lowerDensityBound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The atTop liminf of the real sequence formed by the number of witness integers in the inclusive interval from one to n, divided by n, is at least four fifteenths. This is the lower-density definition used in the conjecture. For every n at least one, fifteen times the count is at least four n. A finite prefix through each stage scale has count C satisfying five C at least three M plus two. Truncating the next two intervals at n gives the bound throughout each interval and gap. The sequence is at most one, and the counting inequality supplies its eventual lower bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_pos`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_step`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.M_strictMono`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.S_pos`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.lowerDensityBound`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.stage_bounds`
- Truth anchor: `D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationDensity.twice_M`
