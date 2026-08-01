# Prime Representation as a Sum of Two Squares

## Abstract

A prime congruent to one modulo four is a sum of two natural squares.

**Theorem 1.1 (A prime congruent to one modulo four is a sum of two squares).**

$$p\ \text{prime}\ \land\ p\equiv 1\ (\operatorname{mod}\ 4)\quad\Rightarrow\quad \exists a,b\in\mathbb{N},\ p=a^2+b^2$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/SumTwoSquares.prime_eq_sq_add_sq_of_mod_four_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p whose remainder modulo four is one, there are natural numbers a and b such that p equals a squared plus b squared. The formal statement retains both the primality and congruence premises and asserts only existence, without adding positivity or uniqueness of the witnesses. The proof installs the explicit primality hypothesis as the local fact required by Mathlib, specializes the standard sum-of-two-squares result after excluding remainder three, and reverses its final equality. No numerical certificate is asserted.
