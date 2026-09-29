# Labelled Retirement Path Data

## Abstract

A finite two-sector path type retains every form label, charge, and parity-specific boundary needed for the literal count.

**Definition 1.1 (Five states and twelve exits).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathData.stepTargets`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathData.stepTargets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

States A, D, E, H, I have respectively four, four, two, one, and one possible next states. This topology is shared by the positive and negative imbalance sectors; it does not identify their directed form labels.

**Definition 1.2 (Positive-sector transition labels).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathData.positiveStepLabel`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathData.positiveStepLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every one of the twelve exits carries an explicit low form, high form, and integer change of imbalance at +1. In state A, for example, the four charges are 1, 2, 0, -1. Separate indices preserve equal-weight but differently labelled transitions.

**Definition 1.3 (Negative-sector transition labels).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathData.negativeStepLabel`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathData.negativeStepLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The negative sector has twelve separately listed form pairs and charges on the same target indices. Its state-A charges are -1, -2, 0, 1; a reciprocal weight symmetry alone cannot recover these labels for the inverse choice map.

**Definition 1.4 (The singleton-ended path type).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathData.OddPath`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathData.OddPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both path types begin with one of two sector-specific class-two labels and recursively choose indexed interior steps. OddPath ends with a single form, while EvenPath ends with an antipodal form pair. The corresponding terminal tables exist only in states A and D; charges add through the complete path.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathData.OddPath`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathData.negativeStepLabel`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathData.positiveStepLabel`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathData.stepTargets`
- Dependency: [D5/S3/Combinatorics/Zigzag/Choices](Choices.md)
