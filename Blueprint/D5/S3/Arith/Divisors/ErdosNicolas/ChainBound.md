# Divisor chain averages

## Abstract

Divisor chain averages

**Theorem 1.1 (Local non-strict chain bounds).**

$$\forall p \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(n \ne 0 \Rightarrow \left(q = 1 \lor \operatorname{Prime}\left(q\right)\right)\right) \Rightarrow \left(q \mid n \Rightarrow \left(\left(n \ne 0 \Rightarrow \left(\neg p \mid n\right)\right) \Rightarrow \left(\forall phi \in \mathbb{N} \to \mathbb{Q},\; \forall c \in \mathbb{Q},\; \left(\forall r \in \mathbb{N},\; q \cdot r \in \operatorname{divisors}\left(n\right) \Rightarrow \left(\left(\neg p \mid r\right) \Rightarrow \operatorname{phi}\left(r\right) + \operatorname{phi}\left(q \cdot r\right) \le 2 \cdot c\right)\right) \Rightarrow \left(\left(\forall r \in \mathbb{N},\; q^{2} \cdot r \in \operatorname{divisors}\left(n\right) \Rightarrow \left(\left(\neg p \mid r\right) \Rightarrow \operatorname{phi}\left(r\right) + \operatorname{phi}\left(q \cdot r\right) + \operatorname{phi}\left(q^{2} \cdot r\right) \le 3 \cdot c\right)\right) \Rightarrow \sum_{d \in \operatorname{divisors}\left(n\right)}\operatorname{phi}\left(d\right) \le c \cdot \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/ChainBound.divisor_chain_average_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

The empty divisor set n=0 needs no multiplier or p-free restriction. For nonzero n, q is either one or prime and p does not divide n. The unit q=1 case follows pointwise from the pair test. For prime q dividing n, split the divisors into q-power chains, each of length at least two. Pair tests are required only when q*r belongs to n.divisors, and triple tests only when q^2*r belongs to n.divisors. Every chain term is p-free, without primality of p. Decomposing each chain length into twos and threes gives the bound. Constant weights c attain equality, so uniform strictness is impossible.

**Theorem 1.2 (Strict local chain bounds).**

$$\forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \left(q = 1 \lor \operatorname{Prime}\left(q\right)\right) \Rightarrow \left(q \mid n \Rightarrow \left(n \ne 0 \Rightarrow \left(\forall phi \in \mathbb{N} \to \mathbb{Q},\; \forall c \in \mathbb{Q},\; \left(\forall r \in \mathbb{N},\; q \cdot r \mid n \Rightarrow \operatorname{phi}\left(r\right) + \operatorname{phi}\left(q \cdot r\right) < 2 \cdot c\right) \Rightarrow \left(\left(\forall r \in \mathbb{N},\; q^{2} \cdot r \mid n \Rightarrow \operatorname{phi}\left(r\right) + \operatorname{phi}\left(q \cdot r\right) + \operatorname{phi}\left(q^{2} \cdot r\right) < 3 \cdot c\right) \Rightarrow \sum_{d \in \operatorname{divisors}\left(n\right)}\operatorname{phi}\left(d\right) < c \cdot \operatorname{card}\left(\operatorname{divisors}\left(n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/ErdosNicolas/ChainBound.divisor_chain_average_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. Erdős and J.-L. Nicolas (1989). *On functions connected with prime divisors of an integer*. URL: <https://oeis.org/A330076>.

*Commentary.*

For nonzero n, let q be one or a prime divisor of n. With q=1 the pair test gives a strict pointwise bound. For prime q, strict pair and triple tests on complete blocks give strict chain sums. The divisor set is nonempty, so summing remains strict. The nonzero condition is necessary: n=0 has no divisors. Composite q can leave isolated divisors; q=n=4 permits a large weight at 2 despite all the local block tests. Lengths two and three both occur, and weights c-epsilon show that c is a sharp supremum.

## References

- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/ChainBound.divisor_chain_average_coprime`
- Truth anchor: `D5/S3/Arith/Divisors/ErdosNicolas/ChainBound.divisor_chain_average_lt`
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/Basic](Basic.md)
- Dependency: [D5/S3/Arith/Divisors/ErdosNicolas/DivisorBlocks](DivisorBlocks.md)
