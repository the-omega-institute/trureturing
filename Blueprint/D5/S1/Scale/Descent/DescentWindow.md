# Pell-Type Descent Window

## Abstract

Two Pell-type square bounds force a strict descent window.

**Theorem 1.1 (Square bounds force the descent window).**

$$\forall c, T\in\mathbb{Z},\ 3 \leq T \land 0 \leq c \land T^2-1 \leq c^2 \land 3\cdot c^2 \leq 4\cdot {T^2-1} \Rightarrow T \leq c \land 3\cdot c < 4\cdot T$$

*Proof.* Machine-checked in Lean as `D5/S1/Scale/Descent/DescentWindow.descent_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let c and T be integers with T at least three and c nonnegative. If T squared minus one is at most c squared, while three times c squared is at most four times T squared minus one, then T is at most c and three times c is strictly less than four times T. The latter is the division-free form of the source window c < 4T/3.

This is the descent-window inequality selected from the source atom. It does not assert the atom's separate orbit-uniqueness or finite-base connectivity claims. The repository and pinned Mathlib were searched for the full implication without an exact hit. A LeanSearch POST query also returned only general square and division inequalities, not this combined theorem. The proof therefore uses integer discreteness, multiplication monotonicity, ring normalization, and Presburger arithmetic locally.

## References

- Truth anchor: `D5/S1/Scale/Descent/DescentWindow.descent_window`
