# First Off-Line Height

## Abstract

Strip-bounded off-line zeros of a nonzero entire function have a first positive height.

**Definition 1.1 (Positive off-line heights).**

Lean statement: `D5/S3/Zeros/FirstOffLineHeight.positiveOffLineHeights`

*Formalization.* `D5/S3/Zeros/FirstOffLineHeight.positiveOffLineHeights` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This set records the positive imaginary parts of zeros whose real part differs from the proposed midline.

**Theorem 1.2 (Existence of the first off-line height).**

$$\begin{aligned}\forall F: \mathbb{C} \to \mathbb{C}, c, B: \mathbb{R}, w: \mathbb{C},\\F\left(w\right) \neq 0 \land 0 \leq B,\\(\forall z, F\left(z\right) = 0 \Rightarrow \left|\operatorname{re}\left(z\right)\right| \leq B) \land \operatorname{Entire}\left(F\right) \land \operatorname{Nonempty}\left(\operatorname{H}\left(F, c\right)\right) \Rightarrow\\\exists T\in \operatorname{H}\left(F, c\right), \forall t\in \operatorname{H}\left(F, c\right), T \leq t.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/FirstOffLineHeight.first_off_line_height_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem makes explicit the bounded-strip hypothesis used by the source's compact-rectangle argument. Entirety alone is insufficient: zeros can escape horizontally while their positive heights tend to zero.

A supplied nonzero value rules out the identically zero function. Mathlib's isolated-zero theorem makes the zero set codiscrete, so its intersection with a compact ball is finite.

Starting from one positive off-line height, the proof restricts to heights below it. The strip bound puts all corresponding zeros in one compact ball, and the minimum of the resulting nonempty finite set is the required first height.

## References

- Truth anchor: `D5/S3/Zeros/FirstOffLineHeight.first_off_line_height_exists`
- Truth anchor: `D5/S3/Zeros/FirstOffLineHeight.positiveOffLineHeights`
