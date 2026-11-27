# Prime Products and Weighted Collision Excess

## Abstract

A common integer shift controls the excess collision mass across prime products.

Take a finite indexed integer spectrum with nonnegative real weights of sum W. Fix natural numbers p, H, D, r, B and Q, with Q at least 2. Give each ordered pair of degree-p count vectors the product of its two weighted multinomial coefficients. Assume that every such pair has absolute integer gap at most D. Let L be the weighted mass of pairs with absolute gap at most H. For a modulus q let C(q) denote the mass of pairs whose gap modulo q is the image of an integer in [−H,H]. Let P be a finite set of primes at least Q. Assume that D+H is strictly less than Q to the power B+1.

Write E for the sum of C(q) minus L over all r-element subsets of P, using the product of the primes in each subset as q. Write choose(n,r) for the binomial coefficient, including the value zero when r exceeds n.

**Theorem 1.1 (An upper bound on the sum of product-modulus excesses).**

$$0 \leq E \leq \operatorname{min}\left(\operatorname{choose}\left(\left|P\right|, r\right), (2 \cdot H+1) \cdot \operatorname{choose}\left(\operatorname{min}\left(B, \left|P\right|\right), r\right)\right) \cdot (W^{2 \cdot p}-L)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/PrimeProductCollisionBudgets.sum_prime_product_cyclic_excess_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an off-band gap d, each product modulus that counts the pair gives one shift y in the band. Every prime in that subset divides the same nonzero integer d−y. The single-prime counting bound at radius zero gives at most B eligible primes for each shift. Take the union of the families of r-element subsets over all 2H+1 shifts and sum the resulting incidence bound against the off-band pair weights.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/PrimeProductCollisionBudgets.sum_prime_product_cyclic_excess_le`
- Dependency: [D5/S3/Fourier/Concentration/PrimeCyclicCollisionBudgets](PrimeCyclicCollisionBudgets.md)
