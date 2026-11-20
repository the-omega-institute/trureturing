# Scaled block masses and stabilizer orders

## Abstract

Factorial divisibility for the masses of a labeled partition.

**Theorem 1.1 (The block factorial product divides each scaled mass).**

$$\forall I k s v, \operatorname{SizeSum}\left(s\right) = k \land \operatorname{Divides}\left(k - 1, \operatorname{Mass}\left(s, v\right)\right) \Rightarrow \forall i, \operatorname{Divides}\left(\operatorname{BlockFactorials}\left(s\right), \operatorname{factorial}\left(k - 2\right) \cdot \operatorname{s}\left(i\right) \cdot \operatorname{v}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility.factorial_product_dvd_scaled_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I be a finite set and k a natural number. The natural size family s has sum k and the natural value family v assigns a value to each block. Mass(s,v) is the sum of the products s(i)v(i), and BlockFactorials(s) is the product of the factorials of the sizes. SizeSum(s) is the sum of the block sizes. If Mass(s,v) is divisible by k minus one, then BlockFactorials(s) divides each block mass multiplied by the factorial of k minus two.

For zero or one label the factorial product is one. For at least two labels, remove one element from the designated block and denote the new sizes by b. Write P for their factorial product. Multinomial integrality gives that P divides the factorial of k minus one. Removing one element from any nonempty block of b gives that P divides the factorial of k minus two times that block's size. Multiply by the block values and sum. Subtraction from the scaled total shows that P divides the scaled value of the original designated block. Multiplying by the original block size restores the full factorial product.

The divisibility hypothesis is necessary for uniform coverage at a fixed positive total when k is at least two. Use block sizes k minus one and one, with values zero and m. The singleton demand is m divided by k minus one.

For equal-coordinate groups of a probability profile, the factorial product is the order of the profile stabilizer. In a regular seed orbit, a stabilizer orbit assigned to a label group of size s(i) contributes the stabilizer order divided by s(i) to each label in the group. The divisibility theorem makes the corresponding block demands integers when the masses are scaled by the factorial of k minus two.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/StabilizerFactorialDivisibility.factorial_product_dvd_scaled_coordinate`
