# Sound certificates for original-residue capacities

## Abstract

Cyclic polynomial encoding certifies actual histogram bounds on the 8640-point six-row transversal. The soundness theorem connects typed arithmetic certificates to all 245 original tail rows; 96 explicit certificates supply every canonical class.

**Definition 1.1 (Packed actual histogram).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.packed`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.packed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum over q in U of 16384 raised to originalResidue i q encodes the original-residue bucket counts.

**Definition 1.2 (Six-row exclusion predicate).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.keep`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.keep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean predicate excludes the six original forms at canonical phases 0,0,c/48,c/24 modulo 2,c/6 modulo 4,c modulo 6.

**Definition 1.3 (Canonical seven-phase vector).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.canonicalPhases`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.canonicalPhases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a class in Fin 96, the first seven phases are 0,0,c/48,c/24 modulo 2,c/6 modulo 4,c modulo 6,0. Tail phases in this representative are zero; the capacity bound allows arbitrary actual tail phases.

**Definition 1.4 (Cyclic histogram projection).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.encodePolynomials`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.encodePolynomials` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each horizontal polynomial, reduction modulo 16384 to the power g minus one collects x modulo g. Digit extraction and remapping by a t + b y modulo g form the packed projected histogram.

**Definition 1.5 (Distinct restricted row queries).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.key`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.key` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal 129 triples give the restricted gcd and the two original coefficient residues for every distinct tail query.

**Definition 1.6 (Original tail index).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.tailIndex`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.tailIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tail index j is 7+j in Fin 252.

**Definition 1.7 (Original row to query map).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.rowKey`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.rowKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each of the 245 original tail rows is assigned its index in the 129-query table. The soundness proof checks the restricted gcd and both coefficient residues.

**Definition 1.8 (Scaled original-row capacity).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.weight`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight is the factor 11 for labels 199 and 2377 or 10 otherwise, multiplied by the restricted gcd and period divided by the original modulus.

**Definition 1.9 (Typed capacity certificate).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.CapacityCertificate`

*Formalization.* `D5/S3/Arith/Covering/Erdos203CapacityCertificate.CapacityCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The certificate carries 24 horizontal encodings, 129 shared residue histograms, histogram bounds and an uncovered-point count. Its proof fields require equality with the actual six-row predicate, the cyclic encoding equations, every digit bound, the count equation and the exact scaled deficit inequality.

**Theorem 1.10 (Soundness for actual finite histograms).**

Lean statement: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.certificate_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203CapacityCertificate.certificate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every class c in Fin 96 and every CapacityCertificate c, the actual histogram maxima satisfy the scaled gap inequality with numerator 41512904387 and denominator 2792167686000. Base-16384 digit extraction equals filtered Finset cardinality because each histogram has at most 8640 points. Cyclic polynomial reduction preserves the residue counts, and every original tail row is mapped to its checked restricted gcd and coefficient residues. This theorem alone has a certificate parameter; the final result discharges it for all 96 classes.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.CapacityCertificate`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.canonicalPhases`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.certificate_bound`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.encodePolynomials`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.keep`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.key`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.packed`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.rowKey`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.tailIndex`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203CapacityCertificate.weight`
- Dependency: [D5/S3/Arith/Covering/Erdos203SixCapacity](Erdos203SixCapacity.md)
