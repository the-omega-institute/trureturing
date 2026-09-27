# The seventh original row and conditional capacities

## Abstract

The original seventh row is x+8y=0 modulo 11. Its removal leaves exactly ten elevenths of every selected union of six-row kernel cosets. The corresponding capacity factor is ten elevenths for all tail rows except the parallel rows labelled 199 and 2377.

**Definition 1.1 (Seventh original form).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The homomorphism originalMap 6 takes values in ZMod 11.

**Definition 1.2 (Explicit inverse residues).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenInverse`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer list 0,1,6,4,3,9,2,8,7,5,10 is indexed by the argument modulo 11; it gives multiplicative inverses at every nonzero residue.

**Definition 1.3 (Preserving translation witness).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenWitness`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If the original modulus is divisible by 11, the translation is an integer multiple of (8640 b,-8640 a). Otherwise it is a multiple of (360 e,0). The multiplier is chosen using elevenInverse; the theorem verifies its exact row constraints.

**Definition 1.4 (Original-row capacity factor).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventhFactor`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventhFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The factor is 11 for prime labels 199 and 2377 and 10 for every other row.

**Definition 1.5 (Region missed by the seventh row).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.sevenRegion`

*Formalization.* `D5/S3/Arith/Covering/Erdos203SeventhCapacity.sevenRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The region consists of points in the selected six-row cosets whose seventh original linear form is nonzero modulo 11.

**Theorem 1.6 (Exact density and compatible original-row bound).**

Lean statement: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh_capacity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every subset U of the 360 by 24 transversal, 11 times 8640 times the region cardinality equals 10 times the cardinality of U times M squared. For every one of the 245 tail rows and every phase in its original modulus, the intersection satisfies the six-row histogram bound multiplied by ten elevenths; the factor is one for labels 199 and 2377. Explicit integer translations preserve the six-row kernel and the original row fiber while cycling the seventh residue. This establishes compatibility on the same actual torus and phase, including nonprimitive restrictions.

## References

- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenInverse`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.elevenWitness`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.sevenRegion`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventhFactor`
- Truth anchor: `D5/S3/Arith/Covering/Erdos203SeventhCapacity.seventh_capacity`
- Dependency: [D5/S3/Arith/Covering/Erdos203SixCapacity](Erdos203SixCapacity.md)
