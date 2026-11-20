# Integer coverage by half-integer weights

## Abstract

Parity limits integer mass coverage when some ternary weights are half-integers.

**Theorem 1.1 (Integer coverage bound with two kinds of weights).**

$$\forall h t L, \operatorname{IntegerCoverage}\left(h, t, L\right) \Rightarrow L \le \frac{3^h + 1}{2} \cdot 3^t$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.mixed_half_weights_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h doubled weights be odd integers and let t other weights be integers. Every weight has a ternary occupancy. If the dot products realize every integer level from zero to L minus one, the count of these levels is bounded by the number of even ternary words on h coordinates times three to the power t.

An integer mass forces the sum of the first h digits to be even. Ternary coding preserves parity because the base is odd. The even code values run from zero through the largest even number below three to the power h. Calibration makes the map of levels to the two occupancy words injective.

To attain the bound for even h, take doubled half-integer weights equal to the first h powers of three. Let W be the number of even ternary codes. Take the remaining t integer weights to be W times the first t powers of three. One plus the total pair mass is W times three to the power t. The total is even.

The quotient and remainder on division by W give the two occupancy words, with the remainder encoded at twice its value. For a positive total, divide the weights by that total. At the midpoint select one seed per pair. Extend the lower events by swapping pairs and taking complements.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.mixed_half_weights_bound`
