# Prime-power divisor blocks

## Abstract

Prime-power divisor blocks

**Theorem 1.1 (A two-block covering of the divisor set).**

$$\forall p \in \mathbb{N},\; \forall a \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{Prime}\left(p\right) \Rightarrow \left(0 < a \Rightarrow \operatorname{divisors}\left(p^{a} \cdot m\right) = \operatorname{union}\left(\operatorname{divisors}\left(m\right), \operatorname{image}\left(\operatorname{mulBy}\left(p\right), \operatorname{divisors}\left(p^{a - 1} \cdot m\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks.prime_power_divisors_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For a prime p and a positive exponent a, every divisor of p^a m either divides m or is p times a divisor of p^(a-1) m. If p divides the divisor, cancel one copy of p; otherwise coprimality removes the prime power. The equality includes m=0, when both sides are empty. The blocks can overlap for general m. Under the additional hypothesis that p does not divide m, they are disjoint, their cardinalities are tau(m) and a tau(m), and their union has cardinality (a+1) tau(m). These are the two sets used by the prime-power kernel criterion.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks.prime_power_divisors_partition`
