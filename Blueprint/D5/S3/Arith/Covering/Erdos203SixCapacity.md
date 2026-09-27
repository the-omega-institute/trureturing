# Conditional capacity after six original rows

## Abstract

This is a proved prerequisite for the 252-row obstruction. It does not certify the seventh-row capacity factor, the 96 numerical deficits, a positive 252-row missed fraction, or the whole Erdos 203 problem.

**Definition 1.1 (Six-row rectangular transversal).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.SixRect`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.SixRect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SixRect is Fin 360 times Fin 24, of cardinality 8640.

**Definition 1.2 (Representative on the full period).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRepresentative`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The representative sends the integer coordinates of q through periodMap.

**Definition 1.3 (Assembling a coset point).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixAssembly`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.sixAssembly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map adds the representative of q to an element of sixTorus.

**Definition 1.4 (Union of selected whole cosets).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRegion`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A torus point z belongs precisely when z minus some sixRepresentative q belongs to sixTorus for a q in U.

**Definition 1.5 (Restricted image gcd).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.restrictedGcd`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.restrictedGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For row i this is gcd(e_i,gcd(360 a_i,228 a_i + 24 b_i)).

**Definition 1.6 (Original residual phase).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.originalResidue`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.originalResidue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For q in SixRect, this is a_i q.1 + b_i q.2 reduced modulo restrictedGcd i.

**Definition 1.7 (Representatives missed by six rows).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixMissed`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.sixMissed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This Finset selects the representatives at which all six original forms differ from the corresponding fixed original phases.

**Definition 1.8 (Original-residue histogram maximum).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.histogramMaximum`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SixCapacity.histogramMaximum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum is computed from the actual original linear form modulo its restricted image gcd on the selected rectangle subset. It is not an assumed capacity oracle.

**Theorem 1.9 (Actual six-row conditional capacity).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SixCapacity.six_row_conditional_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203SixCapacity.six_row_conditional_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rectangle times the six-row kernel maps bijectively to the full torus. The selected missed cosets equal the actual six-row uncovered region. For every subset U, original row and original phase, e times 8640 times the intersection cardinality is at most M squared times g times the largest original-residue histogram bucket in U.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.SixRect`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.histogramMaximum`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.originalResidue`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.restrictedGcd`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixAssembly`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixMissed`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRegion`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.sixRepresentative`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SixCapacity.six_row_conditional_capacity`
- Dependency: [D5/S3/Arith/Covering/Erdos203TorusFibers](Erdos203TorusFibers.md)
