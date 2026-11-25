# The reserve above the weighted Chebyshev tail

## Abstract

A strict all-integer lower reserve for the Robin log margin

**Theorem 1.1 (Lower coefficient 2√2 − 2 at the logarithmic clock).**

$$\forall epsilon \in \mathbb{R},\; 0 < epsilon \Rightarrow \left(\exists Y \in \mathbb{R},\; 16 \le Y \land \left(\forall n \in \mathbb{N},\; Y \le \operatorname{log}\left(n\right) \Rightarrow \frac{2 \cdot \sqrt{2} - 2 - epsilon}{\sqrt{\operatorname{log}\left(n\right)} \cdot \operatorname{log}\left(\operatorname{log}\left(n\right)\right)} < \operatorname{robinLogMargin}\left(n\right) - \operatorname{J}\left(\operatorname{log}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/WeightedTail/SharpReserveLower.sharp_lower_reserve_all_integers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here J(y) is weightedTail psiErrorKernel y. For every positive ε, one real threshold Y ≥ 16 gives the strict reserve at every natural n with log(n) ≥ Y.

For y = log(n), a prime between √y and y/2 pays through its missing first power, its valuation-one Euler gap, or its extra square. In all three cases the payment is bounded below by the minimum of 1/(2p(p+1)) and 1/(2y) − 1/(2p²). Distinct primes charge distinct terms of the exact ledger.

The prime number theorem gives the limiting prime count on each fixed shell at scale √y. Nested finite shells below and above p/√y = √2 give lower contributions arbitrarily close to 3/√2 − 2 and 1/√2, respectively, after multiplication by √y log(y). Their sum is 2√2 − 2. Fixing the shells before taking y large leaves room for the strict inequality.

Independent derivation from the Robin ledger and the unconditional prime number theorem, with no priority claim.

## References

- Truth anchor: `D5/S3/Arith/Robin/WeightedTail/SharpReserveLower.sharp_lower_reserve_all_integers`
- Dependency: [D5/S3/Arith/Robin/PrimeMinCorrectionLower](../PrimeMinCorrectionLower.md)
- Dependency: [D5/S3/Arith/Robin/WeightedTail/PrimeBandReserve](PrimeBandReserve.md)
