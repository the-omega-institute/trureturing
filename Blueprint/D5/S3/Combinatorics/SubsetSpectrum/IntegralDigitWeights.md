# Integral multiples of digit weights

## Abstract

Real digit weights have small integral multiples once calibrated levels exceed the capacity of one fewer coordinate.

**Theorem 1.1 (Integral multiples from a strict count bound).**

$$\forall J b L w x, \operatorname{Calibrated}\left(x, w\right) \land b^{\operatorname{card}\left(J\right) - 1} < L \Rightarrow \forall j:J, \exists d z, 0 < d \land d < b \land d \cdot \operatorname{w}\left(j\right) = z$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/IntegralDigitWeights.exists_integral_multiple_of_capacity_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let J be a finite coordinate type. Suppose the integers from zero through L minus one are all represented by dot products of real weights with digit vectors in Fin b. If L exceeds the number of vectors on all but one coordinate, each weight has an integral multiple by some positive integer strictly below b.

Fix one coordinate and project every calibrated digit vector to the other coordinates. The strict count bound prevents injectivity. Two distinct integer levels with the same projection differ by a nonzero multiple of the weight at the deleted coordinate. The multiplier is the absolute difference of the two digits, so it is less than b.

With two digit values and the strict count bound, the weight itself is an integer. With three digit values and the strict count bound, twice the weight is an integer. In an even-denominator covariant grid, the ternary application uses r exchanged pairs, the weights scaled by the denominator m, and a strict bound of m plus one above three to the power r minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/IntegralDigitWeights.exists_integral_multiple_of_capacity_gap`
