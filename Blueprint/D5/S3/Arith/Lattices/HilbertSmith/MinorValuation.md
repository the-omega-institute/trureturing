# Prime-power layers of Hilbert minors

## Abstract

The Cauchy product for a Hilbert minor has a valuation determined by residue populations.

**Theorem 1.1 (Positive Cauchy product).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive scale, the Cauchy product for any two finite index sets is positive. Its numerator uses only positive differences and its denominator uses positive sums.

**Theorem 1.2 (Exact valuation by residue layers).**

Lean statement: `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_valuation`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_valuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonzero scale and row and column sets of size k within the length-n interval, count the ordinary row residues and the reflected column residues at each positive prime-power layer through the cutoff. Twice the valuation of the Cauchy product equals twice k times the scale valuation minus the logarithmic cutoff, with that difference taken before multiplication, plus the sum of the squared count differences. The cutoff is the base-p logarithm of 2n minus one, with the logarithm taken after subtraction. Doubling the valuation pairs the two orientations of every within-set difference so that the within-set and cross-set counts combine into squares.

## References

- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_pos`
- Truth anchor: `D5/S3/Arith/Lattices/HilbertSmith/MinorValuation.cauchyMinor_valuation`
- Dependency: [D5/S3/Arith/Lattices/HilbertSmith/NestedResidueMatching](NestedResidueMatching.md)
