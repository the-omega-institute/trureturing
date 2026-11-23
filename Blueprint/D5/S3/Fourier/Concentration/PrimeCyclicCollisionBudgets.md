# Prime Moduli and Weighted Collision Excess

## Abstract

A product of shifted gaps bounds the weighted excess caused by modular wraparound.

Take a finite integer spectrum with nonnegative weights w and degree p. Let L be the weighted mass of ordered pairs whose integer gap has absolute value at most the integer H≥0, and C(q) their cyclic band mass modulo q. Write W for the sum of the weights. Let P be a finite set of primes at least Q≥2. Suppose every integer gap has absolute value at most D. For B≥0 assume that Q to the power B+1 exceeds the product of the absolute values of D−y over integers y in [−H,H].

**Theorem 1.1 (An upper bound on the sum of modular excesses).**

$$0 \leq \sum_{q \in P} (\operatorname{C}\left(q\right)-L) \leq \operatorname{min}\left(B, \left|P\right|\right) \cdot (W^{2 \cdot p}-L)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.sum_cyclic_excess_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an off-band pair, every prime modulus that counts it divides the nonzero product of the shifted gaps. The product of all such primes divides that integer. Comparing with powers of Q bounds the number of moduli that count the pair. Changing the order of summation gives the weighted bound.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.sum_cyclic_excess_le`
- Dependency: [D5/S3/Fourier/Concentration/CyclicCollisionCertificate](CyclicCollisionCertificate.md)
