# Erdos 699 Joint Adjacent Cores

## Abstract

Two adjacent congruences force nontrivial factors at three consecutive integers.

**Theorem 1.1 (Three nontrivial adjacent gcds).**

$$\forall B \in \mathbb{Z}, s \in \mathbb{Z},\; \left(\left(\left(\left(\left(5 \le B \land Odd\left(B\right)\right) \land 1 \le s\right) \land s \le B - 1\right) \land 2 \cdot B + 1 \mid 4 \cdot s^{2} - 1\right) \land B \mid \left(s - 1\right) \cdot s \cdot \left(s + 1\right)\right) \Rightarrow \left(\left(1 < gcd\left(B, s - 1\right) \land 1 < gcd\left(B, s\right)\right) \land 1 < gcd\left(B, s + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

B and s are integers. The hypotheses are B at least 5 and odd, 1 <= s <= B-1, (2B+1) divides 4s squared minus 1, and B divides (s-1)s(s+1). Each of the three displayed gcds exceeds 1.

The quotient A=(4s squared minus 1)/(2B+1) satisfies 0<A<2B and A=1 modulo 4. Assuming any one gcd is 1 gives a contradiction after cancellation modulo B. The three nontrivial gcds are pairwise coprime, so B has at least three distinct prime factors. This is a necessary condition in one i=3 slice and does not resolve Erdős 699.

## References

- Truth anchor: `D5/S3/Arith/Erdos699JointAdjacentCores.erdos699_joint_adjacent_gcds`
