# The Half-Factorial Criterion for Minus One

## Abstract

Half of the nonzero residues gives an explicit square root criterion for minus one.

**Theorem 1.1 (The signed half-factorial square, its witness, and its obstruction).**

$$\forall p\in\mathbb{N},\quad p\ \text{prime},\quad m=\frac{p-1}{2}:\quad(p-1)!\equiv(-1)^{m}(m!)^{2}\ (\operatorname{mod}\ p) \land (p\equiv1\ (\operatorname{mod} 4) \Rightarrow (m!)^{2}\equiv-1\ (\operatorname{mod}\ p)) \land (p\equiv3\ (\operatorname{mod} 4) \Rightarrow \neg\exists x\in\mathbb{Z}/p\mathbb{Z},\quad x^{2}=-1)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/HalfFactorial.half_factorial_mod_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p, set m = (p - 1) / 2. The factorial (p - 1)! is congruent to (-1)^m times (m!)^2 modulo p. When p is one modulo four, the specific residue represented by m! squares to minus one; this is an explicit witness, not merely an existence claim. When p is three modulo four, every residue fails to square to minus one.

The prime p = 2 remains inside the first clause: then m = 0 and both sides equal one in ZMod 2. It triggers neither conditional corollary, because two is neither one nor three modulo four.

Library search used pinned Mathlib revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Exact hits were Nat.factorial_mul_descFactorial and ZMod.cast_descFactorial for the factorial split, repository theorem Wilson.wilson_theorem for Wilson's congruence, and ZMod.mod_four_ne_three_of_sq_eq_neg_one for the nonexistence direction. Searches for a theorem already combining factorial, (p - 1) / 2, and the signed square found no matching declaration, so the Lean proof only assembles these existing results.

## References

- Truth anchor: `D5/S3/ArithUnits/HalfFactorial.half_factorial_mod_prime`
