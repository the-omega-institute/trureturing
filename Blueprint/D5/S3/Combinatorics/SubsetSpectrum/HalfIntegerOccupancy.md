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

**Theorem 1.2 (Attainment and normalization for even h).**

$$\forall h t, \operatorname{Even}\left(h\right) \Rightarrow \operatorname{Total}\left(h, t\right) + 1 = \frac{3^h + 1}{2} \cdot 3^t \land \operatorname{Even}\left(\operatorname{Total}\left(h, t\right)\right) \land \operatorname{IntegerCoverage}\left(h, t, \operatorname{Total}\left(h, t\right) + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.mixed_half_weights_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even h, choose doubled half-integer weights equal to the first h powers of three. Put W equal to the number of even codes. The other t weights are W times the first t powers of three. The total pair mass is even, and one plus that total equals W times three to the power t.

For a level k, divide by W. The remainder is encoded by the even word of value twice the remainder, and the quotient by an unrestricted word multiplied by W. The combined mass is k. This supplies every level up to the total.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.mixed_half_weights_bound`
- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/HalfIntegerOccupancy.mixed_half_weights_sharp`
