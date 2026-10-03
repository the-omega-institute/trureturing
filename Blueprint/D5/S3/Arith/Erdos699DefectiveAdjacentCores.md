# Erdos 699 Defective Adjacent Cores

## Abstract

Two congruence conditions force nontrivial factors at three consecutive integers.

**Theorem 1.1 (Three nontrivial adjacent gcds).**

$$\forall b \in \mathbb{Z}, s \in \mathbb{Z},\; \left(\left(\left(\left(\left(\left(\left(5 \le b \land Odd\left(b\right)\right) \land b \equiv 5 (\mathrm{mod} 8)\right) \land b \equiv 8 (\mathrm{mod} 19)\right) \land 1 \le s\right) \land s \le 3 \cdot b - 3\right) \land 6 \cdot b + 1 \mid 4 \cdot s^{2} - 1\right) \land b \mid \left(s - 1\right) \cdot s \cdot \left(s + 1\right)\right) \Rightarrow \left(\left(1 < gcd\left(b, s - 1\right) \land 1 < gcd\left(b, s\right)\right) \land 1 < gcd\left(b, s + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Erdos699DefectiveAdjacentCores.erdos699_defective_adjacent_gcds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

b and s are integers. The hypotheses are b at least 5 and odd, b congruent to 5 modulo 8, b congruent to 8 modulo 19, 1 <= s <= 3b-3, (6b+1) divides 4s squared minus 1, and b divides (s-1)s(s+1). Each of the three displayed gcds exceeds 1.

Writing (6b+1)A=4s squared minus 1 gives 0<A<6b and A congruent to 1 modulo 4. A unit gcd at s gives a square congruent to 5 modulo 8; a unit gcd at s+1 gives an impossible square bound; a unit gcd at s-1 gives a square congruent to 2 or 3 modulo 19. Thus all three adjacent gcds are nontrivial. This is a necessary condition in one Erdos 699 slice and does not resolve the full problem.

## References

- Truth anchor: `D5/S3/Arith/Erdos699DefectiveAdjacentCores.erdos699_defective_adjacent_gcds`
