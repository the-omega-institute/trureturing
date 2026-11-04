# The all-index denominator formula for OEIS A362534

## Abstract

For every positive index, the reduced denominator of the polarization-transfer ratio is the odd binomial gap divided by its greatest common divisor with the ceiling half-index.

**Theorem 1.1 (Exact reduced fractions for every positive index).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall B \in \mathbb{N},\; \forall v \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall G \in \mathbb{N},\; (1 \le n \land \left(m = n - \operatorname{NatDiv}\left(n, 2\right) \land \left(B = \operatorname{choose}\left(n, \operatorname{NatDiv}\left(n, 2\right)\right) \land \left(v = \operatorname{factorization}\left(B, 2\right) \land \left(b = \operatorname{NatDiv}\left(B, 2^{v}\right) \land G = \operatorname{NatDiv}\left(2^{n} - B, 2^{v}\right)\right)\right)\right)\right)) \Rightarrow (\operatorname{num}\left(\operatorname{g}\left(n\right)\right) = G \land \left(\operatorname{den}\left(\frac{\operatorname{f}\left(n\right)}{\operatorname{g}\left(n\right)}\right) = \operatorname{NatDiv}\left(G, \operatorname{gcd}\left(m, G\right)\right) \land \operatorname{num}\left(\frac{\operatorname{f}\left(n\right)}{\operatorname{g}\left(n\right)}\right) = \operatorname{NatDiv}\left(m \cdot b, \operatorname{gcd}\left(m, G\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/DyadicBinomialCancellation.denominator_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The functions f and g are the original rational-valued OEIS formulas from SabbaPolarizationTransferRefutation. For n at least one, let k be floor(n/2), m = n-k, B = choose(n,k), v the exponent of two in B, b = B/2^v and G = (2^n-B)/2^v. Then num(g) = G, den(f/g) = G/gcd(m,G), and num(f/g) = mb/gcd(m,G). The proof derives B strictly between zero and 2^n, hence v < n, positive odd b and G, and coprimality of b and G. The binomial identity n choose(n-1,k) = mB connects the normalized ratio to the original parity definitions. These are exact unbounded arithmetic statements, including n = 1 and n = 2. They do not formalize the physical derivation of either bound. This is the formalization of an existing written correction, not an additional claim of mathematical novelty or a new finite computation.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/DyadicBinomialCancellation.denominator_formula`
- Dependency: [D5/S0/Certificates/SabbaPolarizationTransferRefutation](../../../S0/Certificates/SabbaPolarizationTransferRefutation.md)
