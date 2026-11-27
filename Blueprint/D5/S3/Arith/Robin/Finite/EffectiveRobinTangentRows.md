# Effective Robin tangent rows

## Abstract

Two exact tangent-price rows extend the original finite Robin margin through log height 101.

The row 02 price is 9793/2000000 with literal optimizer 37188534050951960476800 and layer cutoffs 51,9,4,3,2,2,2. Its strict endpoint margins cover 36<=log n<=70.

The row 03 price is 54619/25000000 with literal optimizer 46015447651610234928592313897306120347488000 and layer cutoffs 99,12,5,3,3,2,2,2,2. Its strict endpoint margins cover 70<=log n<=101.

The original Row 01 result covers the lower segment. Concavity of the Robin threshold and exact rational endpoint gaps transfer each fixed-price optimizer certificate to every natural integer in its interval.

**Definition 1.1 (Row 02 price).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Price`

*Formalization.* `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Price` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact row 02 price is 9793/2000000.

**Definition 1.2 (Row 02 optimizer).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Integer`

*Formalization.* `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Integer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact row 02 optimizer is 37188534050951960476800.

**Theorem 1.3 (Row 02 optimality).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal row 02 integer is a Golden Resource optimizer at the row 02 price.

**Theorem 1.4 (Row 02 margin).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive natural integer with log height in [36,70] has positive original Robin log margin.

**Definition 1.5 (Row 03 price).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Price`

*Formalization.* `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Price` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact row 03 price is 54619/25000000.

**Definition 1.6 (Row 03 optimizer).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Integer`

*Formalization.* `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Integer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact row 03 optimizer is 46015447651610234928592313897306120347488000.

**Theorem 1.7 (Row 03 optimality).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal row 03 integer is a Golden Resource optimizer at the row 03 price.

**Theorem 1.8 (Row 03 margin).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_margin`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive natural integer with log height in [70,101] has positive original Robin log margin.

**Theorem 1.9 (Finite margin through height 101).**

Lean statement: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.robin_margin_through_height_101`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.robin_margin_through_height_101` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing Row 01 and the two exact tangent rows imply positive original Robin log margin for every natural n>5040 with log n<=101.

## References

- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.robin_margin_through_height_101`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Integer`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02Price`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_margin`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row02_optimal`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Integer`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03Price`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_margin`
- Truth anchor: `D5/S3/Arith/Robin/Finite/EffectiveRobinTangentRows.row03_optimal`
- Dependency: [D5/S3/Arith/Robin/Finite/RobinRow01](RobinRow01.md)
