# The complete residue image of a cubic Lucas tail

## Abstract

The cubic Lucas tail fills exactly a disjoint collection of full residue fibres at every precision above the first nonconstant period plateau.

**Theorem 1.1 (A single phase fills its entire residue fibre).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phase_image`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phase_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be the seed-block depth, e the base-three Fermat depth, and t the order of nine modulo the seed prime p. Above precision 2h+e, each index phase r modulo t fills every lift of its coarse residue. At an added k digits, the first p^k samples in that phase suffice.

**Theorem 1.2 (The orbit is a union of full fibres).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_total_image`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_total_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An integer occurs at the finer precision if and only if its coarse residue is one of the first t samples. This describes image membership and not merely a recurrence period.

**Theorem 1.3 (The phase fibres are pairwise disjoint).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phases_disjoint`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phases_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first t coarse samples are distinct. Thus each observed fine residue belongs to exactly one of the listed phase fibres.

**Theorem 1.4 (A unique index in one period represents each residue).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_one_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_one_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite orbit has exactly t times p^k residues at the added k digits.

**Theorem 1.5 (Nine explicit coarse residues determine the entire first-prime image).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_nineteen_image`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_nineteen_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the first block prime 19, every higher-precision lift comes from one of nine exact residues modulo 6859. Their values are computed from the cubic recurrence without evaluating large Lucas numbers.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_nineteen_image`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_one_cycle`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phase_image`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_phases_disjoint`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicBlockTailOrbitImage.tailBlock_total_image`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicBlockTailPeriodClosed](GoldenCubicBlockTailPeriodClosed.md)
