# Divided differences over even and odd integer nodes are 2-adic units

## Abstract

Let z be distinct integer nodes indexed by a finite type, even on a set A of indices and odd off A, and let alpha = #A and beta = #A^c. If the binomial coefficient C(alpha + beta - 2, alpha - 1) is odd, then the partial divided-difference sum over the even nodes, the sum over i in A of 1 / prod_{j != i} (z i - z j), is a nonzero rational number of 2-adic valuation 0.

**Theorem 1.1 (The even-node partial sum is a 2-adic unit).**

$$\forall iota \in Type,\; [\operatorname{Fintype}\left(iota\right)], [\operatorname{DecidableEq}\left(iota\right)], \forall z \in iota \to \mathbb{Z},\; \operatorname{Injective}\left(z\right) \Rightarrow (\forall A \in \operatorname{Finset}\left(iota\right),\; \operatorname{Nonempty}\left(A\right) \Rightarrow ((\forall i \in A,\; \operatorname{Even}\left(z\left(i\right)\right)) \Rightarrow ((\forall i \in iota,\; \left(\neg (i \in A)\right) \Rightarrow (\operatorname{Odd}\left(z\left(i\right)\right))) \Rightarrow (\operatorname{Odd}\left(\operatorname{choose}\left(\operatorname{card}\left(iota\right) - 2, \operatorname{card}\left(A\right) - 1\right)\right) \Rightarrow (\sum_{i \in A} (\prod_{j \in \operatorname{erase}\left(\operatorname{univ}, i\right)} ((z\left(i\right) - z\left(j\right) : \mathbb{Z}) : \mathbb{Q}))^{-1} \ne 0 \land \operatorname{padicValRat}\left(2, \sum_{i \in A} (\prod_{j \in \operatorname{erase}\left(\operatorname{univ}, i\right)} ((z\left(i\right) - z\left(j\right) : \mathbb{Z}) : \mathbb{Q}))^{-1}\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.evenOdd_dividedDifference_twoAdicUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write the even nodes as z i = 2 mu i. The sum equals 2^(1 - alpha) times the divided difference, over the integer nodes mu, of g(2 mu) with g(x) = prod_{j not in A} 1 / (x - z j). In the 2-adic integers every z j with j not in A is a unit u_j^(-1), and 1 / (x - z j) agrees at the even nodes, modulo 2^N, with the truncated geometric series -u_j sum_{t < N} (u_j x)^t. The divided difference of mu^i over alpha distinct integer nodes is the coefficient of degree alpha - 1 of the remainder of X^i modulo the monic nodal polynomial: it is an integer, it vanishes for i < alpha - 1 and it equals 1 for i = alpha - 1. Choosing N larger than the 2-adic valuations of the nodal products, the sum is congruent modulo 2 to the coefficient of x^(alpha - 1) in prod_{j not in A} (-u_j sum_{t < N} (u_j x)^t). Modulo 2 this product is (1 + x + ... + x^(N-1))^beta, whose coefficient of degree alpha - 1 is C(alpha + beta - 2, alpha - 1). An odd coefficient makes the sum a 2-adic unit. The binomial index is written card(iota) - 2 with natural-number subtraction, which equals alpha + beta - 2 whenever alpha + beta >= 2; for a single node it is 0, matching the value 1 of the sum.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ParityNodeDividedDifference.evenOdd_dividedDifference_twoAdicUnit`
