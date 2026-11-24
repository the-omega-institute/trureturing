# Prime Moduli and Weighted Collision Excess

## Abstract

A product of shifted gaps bounds the weighted excess caused by modular wraparound.

Take a finite indexed integer spectrum with nonnegative real weights w. Let p, H, D, Q and B be natural numbers. Each ordered pair of degree-p count vectors has weight equal to the product of its two weighted multinomial coefficients. Let L be the mass of pairs with absolute integer gap at most H, and C(q) the mass obtained by testing the gap modulo q against the image of the closed integer band [−H,H]. Write W for the sum of the base weights. Let P be a finite set of primes at least Q, with Q≥2. Suppose every degree-p gap has absolute value at most D. Assume that Q to the power B+1 strictly exceeds the product of |D−y| over the integers y in [−H,H].

**Theorem 1.1 (A count of prime moduli for a single off-band gap).**

$$n \leq B$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.band_alias_card_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one integer gap d with H < |d| ≤ D, n counts the primes in P for which the residue of d is the image of some band shift. Each such prime divides the nonzero product of the absolute shifted gaps.

**Theorem 1.2 (An upper bound on the sum of modular excesses).**

$$0 \leq \sum_{q \in P} (\operatorname{C}\left(q\right)-L) \leq \operatorname{min}\left(B, \left|P\right|\right) \cdot (W^{2 \cdot p}-L)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.sum_cyclic_excess_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an off-band pair, every prime modulus that counts it divides the nonzero product of the shifted gaps. The product of all such primes divides that integer. Comparing with powers of Q bounds the number of moduli that count the pair. Changing the order of summation gives the weighted bound.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.band_alias_card_le`
- Truth anchor: `D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets.sum_cyclic_excess_le`
- Dependency: [D5/S3/Fourier/Concentration/CyclicCollisionCertificate](CyclicCollisionCertificate.md)
