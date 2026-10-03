# Golden Cubic Block Congruences

## Abstract

Congruences and two-adic valuations at the power-of-three golden indices.

**Theorem 1.1 (Lucas residues at cubic block indices).**

Lean statement: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_lucas_block`

*Proof.* Machine-checked in Lean as `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_lucas_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive j, the Lucas number at index 3^j is four modulo seventy-two and has two-adic valuation two. Its square plus three is one modulo nine, and its square is one modulo five. The square plus three is nineteen modulo eighty. The next Lucas value is the current value times its square plus three. The residue statements follow from this cubic recurrence and induction on j.

**Theorem 1.2 (Fibonacci residue at cubic block indices).**

Lean statement: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_fibonacci_block`

*Proof.* Machine-checked in Lean as `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_fibonacci_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive j, the Fibonacci number at index 3^j is two modulo four and has two-adic valuation one. The next Fibonacci value is the current one times the square of the current Lucas value plus one. Its residue follows from this coordinate identity and the Lucas congruence.

**Theorem 1.3 (Interlevel cubic block congruence).**

Lean statement: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_interlevel`

*Proof.* Machine-checked in Lean as `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_interlevel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive earlier index i and later index j, the block formed from the Lucas number at 3^i divides the Lucas number at 3^j. Consequently the later block is three modulo the square of the earlier block. The divisibility propagates through the cubic Lucas recurrence.

**Theorem 1.4 (Product of earlier cubic blocks).**

Lean statement: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_product`

*Proof.* Machine-checked in Lean as `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Lucas number at index 3^j is four times the product of the blocks formed at all positive earlier indices. The identity starts at the Lucas value four at index three and extends one factor at each cubic recurrence step.

## References

- Truth anchor: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_interlevel`
- Truth anchor: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_block_product`
- Truth anchor: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_fibonacci_block`
- Truth anchor: `D5/S1/Scale/GoldenCubicBlockCongruences.golden_cubic_lucas_block`
