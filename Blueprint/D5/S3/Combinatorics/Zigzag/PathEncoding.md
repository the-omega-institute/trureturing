# Encoding Paths as Zigzag Choices

## Abstract

A complete indexed path becomes the original ordered form list, with an exact flow identity connecting accumulated charge to the choice's imbalance.

**Definition 1.1 (Flow of an ordered form list).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathEncoding.formsFlow`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathEncoding.formsFlow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At starting class k, formsFlow sums the directed edge-flow contributions of successive labels. It keeps list order and each label; it is the bridge from the recursive path type to the exact class-by-class integer imbalance.

**Theorem 1.2 (Even path flow reaches the antipodal boundary).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathFlow_eq_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathFlow_eq_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After 3r-3 interior steps and the antipodal form pair, the full n=6r path flow is boundaryFlow of its recorded charge. The proof inducts over labelled tails, applies Retirement's transition identity, then uses the even terminal flow theorem.

**Theorem 1.3 (Odd path flow reaches the singleton boundary).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathEncoding.oddPathFlow_eq_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/PathEncoding.oddPathFlow_eq_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The n=6r+3 path has 3r-1 interior steps and one central terminal form. Its full flow is the boundaryFlow of its charge. The distinct odd terminal identity is necessary here; no closure of an edge cycle is used.

**Definition 1.4 (Encode an even path as an actual choice).**

Lean statement: `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathChoices`

*Formalization.* `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathChoices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The start, each low/high transition pair, and the antipodal terminal are flattened into exactly one form for each source class. The first-class restriction follows from its start index. The oddPathChoices definition performs the corresponding singleton construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathChoices`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathEncoding.evenPathFlow_eq_boundary`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathEncoding.formsFlow`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/PathEncoding.oddPathFlow_eq_boundary`
- Dependency: [D5/S3/Combinatorics/Zigzag/Retirement](Retirement.md)
