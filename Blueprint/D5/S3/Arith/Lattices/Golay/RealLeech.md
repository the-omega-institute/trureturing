# The actual Golay construction as a positive even unimodular real lattice

## Abstract

The actual Golay construction as a positive even unimodular real lattice

**Definition 1.1 (The exact real image of the original integer subgroup).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.lattice`

*Formalization.* `D5/S3/Arith/Lattices/Golay/RealLeech.lattice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lattice is the image under coordinate inclusion of IntegerLeech.integerLattice for the explicit GolayEncoder.code. The form is the real coordinate dot product divided by eight. The dot-over-eight form has the same normalization as the real coordinate dot product after coordinate division by the square root of eight.

**Theorem 1.2 (Membership preserves the actual construction).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.mem_lattice`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLeech.mem_lattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real member has an integer representative satisfying the original Admissible predicate, and every such representative lies in the image.

**Theorem 1.3 (Actual norms are even).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.even_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLeech.even_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing squareSum_div_sixteen theorem supplies the even norm with no new divisibility assumption.

**Theorem 1.4 (The actual pairing is integral).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.integral_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLeech.integral_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing pairing_integral theorem supplies an integer value for every pair of real image points.

**Theorem 1.5 (The actual real lattice is selfdual).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.self_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLeech.self_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All binary hypotheses are discharged by the existing explicit Golay code. The exact original integer representation supplies raw membership, and its existing integral pairing theorem supplies the converse dual inclusion. No real selfduality, determinant, index or covolume is used as a premise.

**Theorem 1.6 (Rank twenty-four integral charges preserve the full form).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLeech.exists_positive_even_unimodular_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLeech.exists_positive_even_unimodular_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinate integer lattice contains the actual image discretely, while the actual eight-coordinate probes prove full real span. The native integer lattice basis gives LatticeData of rank twenty-four with positive definite even integral Gram matrix and unit determinant, together with a charge linear equivalence into the actual image preserving the full dot-over-eight pairing. This establishes lattice data only; the holomorphic VOA, Monster action, CFT and string or holographic realizations require further mathematical constructions.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.even_norm`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.exists_positive_even_unimodular_gram`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.integral_pairing`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.lattice`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.mem_lattice`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLeech.self_dual`
- Dependency: [D5/S3/Arith/Lattices/Golay/DirectLeechDuality](DirectLeechDuality.md)
- Dependency: [D5/S3/Arith/Lattices/Golay/IntegerLeech](IntegerLeech.md)
- Dependency: [D5/S3/Arith/Lattices/Golay/RealLatticeGram](RealLatticeGram.md)
